# Shape Metrics Brazil
# Guillermo Alves
# Mauro Castiella

# PURPOSE: This script delimits the urban shape of municipalities of Brazil, polygonizes them and calculates the metrics.
# This script calculates 12 different metrics that quantify a specific
# aspect of a polygon's shape. A normalized version of each metric is provided
# that is not influenced by the polygon's area. Normalization is done using
# the circle which is the most compact shape possible for a given area.


import geopandas as gpd
import pandas as pd
from shapely.ops import unary_union
from shapely.geometry import Polygon

import processing
import os
from qgis.core import (
    QgsProject,
    QgsVectorLayer,
    QgsGeometry,
    QgsPointXY,
    QgsApplication,
    QgsFeatureRequest,
    QgsRasterLayer,
    QgsProcessingFeedback,
    QgsProcessing,
    QgsProcessingContext,
    QgsStyle,
    QgsPoint,
    QgsFeature,
    QgsRasterFileWriter,
    QgsCoordinateTransformContext,
    QgsVectorFileWriter,
    QgsCoordinateReferenceSystem,
    QgsCoordinateTransform,
    QgsMessageLog, 
    Qgis,
    QgsField
)

from qgis.utils import plugins
import math
import time
import random
from math import radians, sin, cos, sqrt, atan2
import os
from PyQt5.QtCore import QVariant
from PyQt5.QtWidgets import QApplication, QPushButton, QMessageBox
from PyQt5.QtCore import QTimer
from PyQt5 import QtWidgets
from PyQt5.QtCore import QSettings

random.seed(1000)

# Función para agregar campos a una capa
def add_fields(layer):
    """
    Agrega campos a la tabla de atributos de una capa.
    """
    layer.startEditing()
    fields = [
        QgsField("ID", QVariant.Int),
        QgsField("Cohesion", QVariant.Double),
        QgsField("nCohesion", QVariant.Double),
        QgsField("Proximity", QVariant.Double),
        QgsField("nProximity", QVariant.Double),
        QgsField("Spin", QVariant.Double),
        QgsField("nSpin", QVariant.Double),
        QgsField("Exchange", QVariant.Double),
        QgsField("nExchange", QVariant.Double),
        QgsField("Perimeter", QVariant.Double),
        QgsField("nPerimeter", QVariant.Double),
        QgsField("Interior", QVariant.Double),
        QgsField("nInterior", QVariant.Double),
        QgsField("Depth", QVariant.Double),
        QgsField("nDepth", QVariant.Double),
        QgsField("Dispers_", QVariant.Double),
        QgsField("nDispers_", QVariant.Double),
        QgsField("Range", QVariant.Double),
        QgsField("nRange", QVariant.Double),
        QgsField("Girth", QVariant.Double),
        QgsField("nGirth", QVariant.Double),
        QgsField("Traversal", QVariant.Double),
        QgsField("nTraversal", QVariant.Double),
    ]
    layer.dataProvider().addAttributes(fields)
    layer.updateFields()
    layer.commitChanges()



# ------------------------------------------------------------------
def ConvertToGridPnts(ShpGeom, gridTxtFile):
    """
    Converts MultiPolygon or Polygon geometry to a grid of points and writes to a text file.
    
    Parameters:
        ShpGeom: QgsGeometry
            Geometry object of the feature.
        gridTxtFile: str
            Path to the output text file.
    
    Returns:
        tuple: (list of perimeter vertex lists, list of feature points, cell size, x-offset, y-offset)
    """
    # Handle MultiPolygon geometries
    if ShpGeom.isMultipart():
        polygons = ShpGeom.asMultiPolygon()  # Extract individual polygons
    else:
        polygons = [ShpGeom.asPolygon()]  # Wrap single polygon in a list for uniformity

    # Ensure there is at least one polygon
    if not polygons or len(polygons[0]) == 0:
        raise ValueError("Invalid geometry: no polygons found.")

    # Get bounding box and adjust for origin shift
    extent = ShpGeom.boundingBox()
    x_offset, y_offset = extent.xMinimum() + 1, extent.yMinimum() + 1

    extent = [
        extent.xMinimum() - x_offset,
        extent.yMinimum() - y_offset,
        extent.xMaximum() - x_offset,
        extent.yMaximum() - y_offset,
    ]
    print(f"Adjusted extent: {extent}")

    # Process perimeter vertices for all parts of the geometry
    pntLst = []  # Stores feature arrays (rings)
    for polygon in polygons:
        for ring in polygon:
            ring_adj = [[point[0] - x_offset, point[1] - y_offset] for point in ring]
            pntLst.append(ring_adj[::-1] if len(pntLst) > 0 else ring_adj)  # Reverse interior rings

    # Feature area
    a = ShpGeom.area()

    # Desired shape area in pixels
    numPix = 20000

    # Calculate pixel size
    cellsize = (a / numPix) ** 0.5

    # Get min/max coordinates
    minX, minY, maxX, maxY = extent

    # Offset grid by half a pixel
    minX -= cellsize / 2
    maxY += cellsize / 2

    # Prepare for writing grid file
    featPntLst = []  # List of coordinates for points inside the feature
    nrows = 0

    with open(gridTxtFile, "w") as o_grid:
        # Placeholder for header lines
        o_grid.write("\n" * 100)

        # Start at the top of the grid
        Y = maxY

        while Y >= minY:
            nrows += 1  # Row count
            line = ""  # Initialize line for current row
            rangeLst = bounds(pntLst, Y)  # Get X ranges for the current Y coordinate

            # Iterate through columns
            X = minX
            ncols = 0
            while X <= maxX:
                ncols += 1
                for x1, x2 in rangeLst:
                    if x1 <= X <= x2:
                        line += "1 "  # Pixel is inside the feature
                        featPntLst.append([X, Y])
                        break
                else:
                    line += "0 "  # Pixel is outside the feature

                # Increment X coordinate
                X += cellsize

            # Add row to the grid file
            line += "\n"
            o_grid.write(line)

            # Decrement Y coordinate for next row
            Y -= cellsize

    # Add header information to the grid file
    ll_Y = maxY - (nrows - 1) * cellsize - cellsize / 2
    ll_X = minX - cellsize / 2

    with open(gridTxtFile, "r+") as o_grid:
        header = (
            f"ncols {ncols}\n"
            f"nrows {nrows}\n"
            f"xllcorner {ll_X}\n"
            f"yllcorner {ll_Y}\n"
            f"cellsize {cellsize}\n"
            f"NODATA_value -9999\n"
        )
        o_grid.seek(0)
        o_grid.write(header)

    return pntLst, featPntLst, cellsize, x_offset, y_offset



#------------------------------------------------------------------
# IDENTIFY GRID CELLS IN ROW THAT BOUND ROW PIXELS IN FEATURE...

def bounds(studyArea_pntLst,Y):

    # list of intersections between horizontal line and feature...
    intersectLst = []

    for ringLst in studyArea_pntLst:

        # for each position in feature point list...
        for pos in range(len(ringLst)-1):

            # XY coordinates of perimeter segment endpoints...
            X1, Y1 = ringLst[pos][0], ringLst[pos][1]
            X2, Y2 = ringLst[pos+1][0], ringLst[pos+1][1]      

            #---------------------------------------
            # equation for perimeter segment...

            # if vertical perimeter segment
            if X1 == X2:
                # if test Y not in range of perimeter segment, there is no intersection
                if not(Y1 <= Y <= Y2 or Y2 <= Y <= Y1):
                    continue
                # if Y in range, set x value of intercept
                x = X1

            # if perimeter segment not vertical
            else:
                # perimeter segment slope
                m = (Y2-Y1)/(X2-X1)      

                # intercept of segment
                B1 = Y1-(m*X1)

                # if slope equals zero, there can be no intersection...
                if m == 0:
                    continue

                # calculate x of interscept
                x = (Y - B1) / m

                # skip if intersection not on perimeter segment...
                if not(X1 <= x <= X2 or X2 <= x <= X1): continue

            # add intersection X coordinate to list...
            intersectLst.append(x)

    # sort list in ascending order...
    intersectLst.sort()

    #-----------------------------
    # CREATE FINAL RANGE LIST...

    # For each pair of consecutive X values, check if line segment is contained within the shape...
    # final list of ranges (between each set of X values is the inside of shape)...
    rangeLst = []

    # for each pos in intersection list...
    for pos in range(len(intersectLst)-1):

        # X coordinates...
        X1, X2 = intersectLst[pos], intersectLst[pos+1]

        # X coordinate of segment midpoint...
        Xm = X1 + (X2-X1)/2

        # if segment midpoint is in shape, add range to list...
        if pntInShp(studyArea_pntLst,[Xm,Y]) == 1:
            rangeLst.append([X1,X2])

    return rangeLst


#-----------------------------------------------------------------------------
# TEST IF POINT IS IN POLYGON (HELPER ALGORITHM)

# To test if a point is in a shape, a vertical line is drawn from the point to the lowest extent. The number of intersections between the vertical line and
# the shape perimeter is determined. If the number of intersections is more than zero and is odd, then the test point is in the shape.


# requires list of feature XY coordinates
# requires a coordinates for a test point

def pntInShp(pntLst,testPnt):   
    
    # XY coordinates of the test point...   
    Xr, Yr = testPnt[0], testPnt[1]
    
    ringNo = 0

    for ringList in pntLst:

        intersect = 0    # number of intersections
        inPoly = 0
        

        # for each point in feature part...
        for i in range(len(ringList)-1):

            # get X coordinates of segment end points...
            X1,X2 = ringList[i][0], ringList[i+1][0]

            # skip if test point is to the left or right of segment...
            if Xr < X1 and Xr < X2: continue
            if Xr > X1 and Xr > X2: continue
         

            # get Y coordinates of segment end points...
            Y1,Y2 = ringList[i][1], ringList[i+1][1]

            # skip if test point is below segment...
            if Yr < Y1 and Yr < Y2:
                continue

            # if X values are the same, skip...
            if X1 == X2: continue

            # if perimeter segement is vertical, then line must be on it...
            if Y1 == Y2:
                intersect += 1   # count intersection
                continue

            # slope of line between pt1 and pt2...
            m = (Y2-Y1) / (X2-X1)

            # y value on line that has X value equal to test point X coordinate...
            y = m*(Xr-X1)+Y1


            # if test point Y is greater than y on the line between pt1 and pt2...
            if Yr >= y:
                # then vertical line containing test point intersects polygon boundary...
                intersect += 1

        # if more than 1 intersection and total number is odd,
        if intersect > 0 and intersect % 2 != 0:
            # then test point is inside polygon...
            inPoly = 1

##        print (ringNo,inPoly)

        if ringNo == 0 and inPoly == 0: break

        if ringNo > 0 and inPoly == 1:
            inPoly = 0
            break

        ringNo += 1

    else:
        inPoly = 1
       
    return inPoly   # 1 if test point is in shape, 0 if not in shape


#---------------------------------------------------------------------------

## SECTION 3: COHESION FUNCTION

# The average distance between all pairs of points in the shape. Estimated using 30 samples of 1000 points...

def interpointDistance(ptList): # requires list of XY coordinates of points in shape

    # number of points in shape...
    numPts = len(ptList)

    samplSize = 1000    # number of points in sample
    samples = 30        # number of samples
        
    avgD = 0    # average interpoint distance

    # run specified number of samples...
    for t in range(samples):

        total_D = 0     # cumulative distance
        cnt = 0         # number of calculations
        
        # select a random sample of shape points...
        sampLst = random.sample(ptList, samplSize)

        # for each point in sample, calculate distance between it and
        # every other point...
        for pt1 in sampLst:
            
            # get coordinates of a point...   
            X1 = pt1[0]
            Y1 = pt1[1]

            # calculate distance to all other points in sample...
            for pt2 in sampLst:

                # skip pt2 if it is the same as pt1...
                if pt1 == pt2: continue 

                # get coord. of point from sample...
                X2 = pt2[0]
                Y2 = pt2[1]

                # calculate distance to pt1...
                dist = ((X1-X2)**2 + (Y1-Y2)**2)**.5
                
                # cumulative interpoint distance...
                total_D += dist

                # number of calculations...
                cnt += 1
                    
        # average interpoint distance...
        avgD += (total_D / cnt) / samples
         
    return avgD


#----------------------------------------------------------------------
# PROXIMITY INDEX

def proximity(featPntLst,center,r):

    Xc,Yc = center[0], center[1]

    sumD = inPix = 0    # sum of distances

    # for each feature point...
    for X,Y in featPntLst:

        # distance to center...
        d = ((X-Xc)**2 + (Y-Yc)**2)**.5

        sumD += d

        # if distance < EAC radius, then pixel is in
        if d < r:
            inPix += 1  # count pixel

    # calculate average distance
    D_to_Center = sumD / len(featPntLst)

    return D_to_Center, inPix


#----------------------------------------------------------------------
## SECTION 9: THE SPIN INDEX (RELATIVE MOMENT OF INERTIA)...

def spin(XYLst,centroidXY):

    # XY coordiantes of shape centroid...
    Xc, Yc = centroidXY[0], centroidXY[1]

    # sum of distance squared...
    sum_dsqr = 0

    # count of number of pixels...
    cnt = 0

    # for each shape point...
    for pt in XYLst:

        # XY coordiante of point...
        X, Y = pt[0], pt[1]

        # distance to center squared...
        dsqr = (X-Xc)**2+(Y-Yc)**2
        
        # sum of squared distances...
        sum_dsqr += dsqr

        # count of points...
        cnt += 1

    return sum_dsqr / cnt


#---------------------------------------------------------------------------
# GET LIST OF POINTS EVENLY SPACED ALONG PERIMETER
# Vertices not preserved...

def PerimeterPnts(coordLst, numPnts):

    perimPntLst_allRings = []

    totalPerim = 0    

    ringPerimLst = []

    for ringLst in coordLst:

        # perimeter length...
        perim = 0

        # for each perimeter segment, add lengths...
        for pos in range(len(ringLst)-1):
            x1,y1 = ringLst[pos][0], ringLst[pos][1]
            x2,y2 = ringLst[pos+1][0], ringLst[pos+1][1]
            d = ((x1-x2)**2 + (y1-y2)**2)**.5
            perim += d

        ringPerimLst.append(perim)
        totalPerim += perim

    spacingLst = []

    for perim in ringPerimLst:
        rNumPnts = int((perim / totalPerim) * numPnts)
        if rNumPnts == 0: 
            d = rNumPnts = 0
        else:
            d = perim / rNumPnts
            if d < .5: d = .5
        spacingLst.append([d, rNumPnts])

    
    # for each ring in polygon...
    for ringNo in range(len(coordLst)):

        ringLst = coordLst[ringNo]
        d = spacingLst[ringNo][0]
        numPnts = spacingLst[ringNo][1]
        
        if numPnts == 0: continue
        
        #---------------------------------
        # GENERATE POINTS ALONG PERIMETER OF CURRENT RING...

        # list of selected points...
        perimPntLst = []

        # position in vertex list...
        pos = done = 0

        # endpoint coordinates of first perimeter segment...
        X1,Y1 = ringLst[pos][0], ringLst[pos][1]
        X2,Y2 = ringLst[pos+1][0], ringLst[pos+1][1]


        # for each point desired...
        #for pntNum in range(numPnts+15):
        while True:
                   
            # determine the min and max X values for the segment...
            xLst = [X1,X2]
            xLst.sort()
            xMin = xLst[0]
            xMax = xLst[-1]

            # determine the min and max Y values for the segment...
            yLst = [Y1,Y2]
            yLst.sort()
            yMin = yLst[0]
            yMax = yLst[-1]

            # 1 = valid point found; 0 = no valid point found...
            pnt1 = pnt2 = 0
            
            # if segment slope is nearly vertical...
            if abs(X1 - X2) < abs(Y1-Y2)/100:
                x1 = x2 = X1    
                y1 = Y1 - d      
                y2 = Y1 + d
                
            # if segment slope is horizontal...
            elif Y2-Y1 == 0:
                y1 = y2 = Y1
                x1 = X1 - d
                x2 = X1 + d

            # if segment is not nearly vertical, calculate slope and y-intercept
            else:
            
                m = (Y2-Y1) / (X2-X1)    # slope
                b = Y1-(m*X1)            # y-intercept

               
                #---------------------------
                # find point on line that is distance d from (X1,Y1)...

                # coefficients in the quadratic equation...
                A = 1+m**2
                B = 2*m*b - 2*X1 - 2*Y1*m
                C = X1**2 - d**2 + Y1**2 - 2*Y1*b + b**2

                # calculate x intercepts using quadratic equation...
                x1 = (-B + (B**2-4*A*C)**.5) / (2*A)
                y1 = m*x1+b

                x2 = (-B - (B**2-4*A*C)**.5) / (2*A)
                y2 = m*x2+b

            # check if 1st point is on the segment...
            if xMin <= x1 <= xMax:
                if yMin <= y1 <= yMax:
                    # check if point is a vertex...
                    if ((x1-X2)**2 + (y1-Y2)**2)**.5 < .00001:
                        pos += 1
                        # if position is last vertex, analysis is finished...
                        if pos >= len(ringLst)-1:
                            break
                        X2,Y2 = ringLst[pos+1][0], ringLst[pos+1][1]
                    pnt1 = 1

            # check if 2nd point is on the segment...
            if xMin <= x2 <= xMax:
                if yMin <= y2 <= yMax:
                    # check if point is a vertex...
                    if ((x2-X2)**2 + (y2-Y2)**2)**.5 < .00001:
                        pos += 1
                        # if position is last vertex, analysis is finished...
                        if pos >= len(ringLst)-1:
                            break
                        X2,Y2 = ringLst[pos+1][0], ringLst[pos+1][1] 
                    pnt2 = 1

            
                    
            #---------------------------
            
            dNext = d  # additional distance needed (set to full separation distance initially)...

            # if neither point is on line segment, move along successive segments...        
            while pnt1 == pnt2 == 0:

                # calculate additional distance needed to meet spacing requirement...   
                dNext = dNext-((X1-X2)**2 + (Y1-Y2)**2)**.5

                # move position to next vertex (to get next segment)...
                pos += 1

                # if position is last vertex, analysis is finished...
                if pos >= len(ringLst)-1:
                    break

                # if close to vertex, take vertex as the point...
                if dNext < .0001:
                    x1,y1 = X2,Y2
                    X2,Y2 = ringLst[pos+1][0], ringLst[pos+1][1]
                    pnt1 = 1
                    break
            
                # coordinates of next perimeter segment...
                X1,Y1 = ringLst[pos][0], ringLst[pos][1]
                X2,Y2 = ringLst[pos+1][0], ringLst[pos+1][1]

                # determine the min and max X values for the segment...
                xLst = [X1,X2]
                xLst.sort()
                xMin = xLst[0]
                xMax = xLst[-1]

                # determine the min and max Y values for the segment...
                yLst = [Y1,Y2]
                yLst.sort()
                yMin = yLst[0]
                yMax = yLst[-1]

                # 1 = valid point found; 0 = no valid point found...
                pnt1 = pnt2 = 0

                # if segment slope is nearly vertical...
                if abs(X1 - X2) < abs(Y1-Y2)/100:
                    x1 = x2 = X1
                    y1 = Y1 - dNext
                    y2 = Y1 + dNext

                # if segment is not nearly vertical, calculate slope and y-intercept
                else:                
                    if X2!=X1:
                        m = (Y2-Y1) / (X2-X1)
                        b = Y1-(m*X1)

                    #---------------------------
                    # find point on line that is distance d from (X1,Y1)...

                    # coefficients in the quadratic equation...
                    A = 1+m**2
                    B = 2*m*b - 2*X1 - 2*Y1*m
                    C = X1**2 - dNext**2 + Y1**2 - 2*Y1*b + b**2
                  
                    # calculate x intercepts using quadratic equation...
                    x1 = (-B + (B**2-4*A*C)**.5) / (2*A)
                    y1 = m*x1+b

                    x2 = (-B - (B**2-4*A*C)**.5) / (2*A)
                    y2 = m*x2+b

                # check if 1st point is on the segment...
                if xMin <= x1 <= xMax:
                    if yMin <= y1 <= yMax:
                        pnt1 = 1      

                # check if 2nd point is on the segment...
                if xMin <= x2 <= xMax:
                    if yMin <= y2 <= yMax:
                        pnt2 = 1
                        
            # if position is last vertex, analysis is finished...
            if pos >= len(ringLst)-1:
                break

            # if point 1 is valid, and not already in list, add to list
            if pnt1 == 1:
                if [x1,y1] not in perimPntLst:
                    perimPntLst.append([x1,y1])

            # if point 2 is valid, and not already in list, add to list
            elif pnt2 == 1:
                if [x2,y2] not in perimPntLst:
                    perimPntLst.append([x2,y2])

            # set 1st endpoint to last perimeter point...
            X1,Y1 = perimPntLst[-1][0], perimPntLst[-1][1]

        # add last vertex point to perimeter point list...
        perimPntLst.append(ringLst[-1])

        perimPntLst_allRings.append(perimPntLst)

    return perimPntLst_allRings

#-----------------------------------------------------------------------------

# SECTION 13: CALCULATE PIXEL DISTANCE TO PERIPHERY (for depth and girth indices)...

def pt_distToEdge(featPntLst,perimPntLst):

    pt_dToE = []    # list for pixel distances to nearest edge pixel
    perimPnts = []

    for ringLst in perimPntLst:
        perimPnts.extend(ringLst)

    # for each pixel in shape...
    for X1,Y1 in featPntLst:

        dLst = []   # list of distances from shape pixel to all edge pixels

        # for each edge pixel
        for X2,Y2 in perimPnts:

            # calculate distance between shape and perimeter...
            d = ((X1-X2)**2 + (Y1-Y2)**2)**.5

            # add distance to list...
            dLst.append(d)

        # sort distance list to get minimum distance...
        dLst.sort()

        # add minimum distance to list...
        pt_dToE.append(dLst[0])

    return pt_dToE


#-----------------------------------------------------------------------------
## SECTION 14: THE DEPTH INDEX (DISTANCE TO EDGE OF SHAPE)...
def depth(pt_dToE):

    depth = 0
    
    cnt = len(pt_dToE)

    # for each distance in list...
    for d in pt_dToE:
        
        # calculate average of distances...
        depth += d / cnt

    return depth


#-----------------------------------------------------------------------------
## SECTION 15: THE GIRTH INDEX (MAX RADIUS OF INSCRIBED CIRCLE)
def girth(pt_dToE):

    # copy pixel distance to edge list...
    sortLst = pt_dToE[:]

    # sort list to identify maximum distance
    sortLst.sort()
    shp_Girth = sortLst[-1] # max distance to edge...

    # identify position of inmost point in pt_dToE list...
    ptPos = pt_dToE.index(shp_Girth)

    return shp_Girth


#----------------------------------------------------------------
# VIABLE INTERIOR INDEX - the area of the shape that is farther than the edge width distance from the perimeter.


def Interior(pt_dToE, edge_width):

    interiorArea = 0
   
    for d in pt_dToE:
        if d > edge_width:
            interiorArea += 1
            
    return interiorArea

#-----------------------------------------------------------------------------

# SECTION 16: THE DISPERSION INDEX...

# Calculates average distance between points on the perimeter to the proximate center. Points in perimeter should be uniformly distributed...
# requires list with XY of proximate center and a list with XY for perimeter points...

def dispersion_fnc(center,perimPntLst):

    sumD = 0
    dList = []

    # XY coordinates of center...
    Xc, Yc = center[0], center[1]

    # for point in shape perimeter...
    for X1,Y1 in perimPntLst:

        # calculate distance to proximate center...
        d = ((X1-Xc)**2+(Y1-Yc)**2)**.5

        # add distance to list...
        dList.append(d)

        # cumulative distance...
        sumD += d

    # number of points in list...
    numPts = len(dList)

    # average distance from center to perimeter...
    avgD = sumD / numPts

    # calculate std deviation between distances...
    V = 0

    for d in dList:
        V += abs(d - avgD)  # cumulative std deviation (difference between distance and average distance)


    # calculate dispersion index
    ## avgVi = V / (2 * numPts)    # std deviation / 2n
    avgVi = V / (numPts)
    dispersionIndex = (avgD - avgVi)/avgD

    return dispersionIndex, avgD
    
#-----------------------------------------------------------------------------

# SECTION 17: CREATE CONVEX HULL (FOR USE IN THE DETOUR INDEX)...

    ## The ConvexHull algorithm was borrowed from BoundingContainers.py written by:

        #  Dan Patterson
        #  Dept of Geography and Environmental Studies
        #  Carleton University, Ottawa, Canada
        #  Dan_Patterson@carleton.ca
        #
        # Date  Jan 25 2006

    ## Starting with a point known to be on the hull -- leftmost point -- test every 3 consecutive points to see if they form right-hand turns. For any set
    ## of 3 consecutive points that does not form a right-hand turn, then the middle point is not part of the hull - it is not included in the hull list.
    ## The points of the upper hull are derived in the 1st section, points in the
    ## lower hull are derived in the 2nd section. Both sets of points are combined to form the complete hull list.

def ConvexHull(vertexLst):

    hullPoints_allParts = []

    pntLst = vertexLst[:]

    pntLst.sort()  # sort vertex points in ascending order

    #------------------------------------------------
    # Build upper half of the hull (leftmost point to rightmost point in hull).

    upperLst = [pntLst[0], pntLst[1]]   # add 1st two points to upperLst

    # for all points except 1st two...
    for p in pntLst[2:]:
        upperLst.append(p)     # add point to upper list

        # check if last 3 points in the lowerLst form a right-hand turn
        # (must be more than 2 points in lowerLst)...
        while len(upperLst) > 2 and right_turn(upperLst[-3:]) == 0:
            # delete the middle of the 3 points if they do not form a right-hand turn...
            del upperLst[-2]
    
    # Build lower half of the hull (rightmost point to leftmost point in hull).
    pntLst.reverse()  # sort pntLst in descending order
    lowerLst = [pntLst[0], pntLst[1]]
    
    for p in pntLst[2:]:
        lowerLst.append(p)  # add point to lower list

        # check if last 3 points in the lowerLst form a right-hand turn
        # (must be more than 2 points in lowerLst)...
        while len(lowerLst) > 2 and right_turn(lowerLst[-3:]) == 0:
            # delete the middle of the 3 points if they do not form a right-hand turn... 
            del lowerLst[-2]  
    
    # remove duplicates...
    del lowerLst[0]
    del lowerLst[-1]

    # combine upperLst and lowerLst...
    hullPoints = upperLst+lowerLst

    #-----------------------------------------
    # get total perimeter of convex hull...

    hullPerim = 0    # length of hull perimeter

    # for each point in hull...
    for pos in range(len(hullPoints)):

        # starting point of segment...
        X1, Y1 = hullPoints[pos][0], hullPoints[pos][1]

        # endpoint of segment
        if pos+1 < len(hullPoints)-1:
            X2, Y2 = hullPoints[pos+1][0], hullPoints[pos+1][1]   # next point in list
        else:
            X2, Y2 = hullPoints[0][0], hullPoints[0][1]   # 1st point in list (completes final segment)

        # add distance of current hull segment
        hullPerim += ((X1-X2)**2 + (Y1-Y2)**2)**.5
    
    return hullPerim

# ---------------------------------------------------------------------------

# HELPER ALGORITHM (CONVEX HULL): RIGHT-HAND TURN TEST

# Tests if 3 consecutive points form a right hand turn...

def right_turn(pts):

    ## right_turn algorithm borrowed from BoundingContainers.py by Dan Patterson.

    # for three points p, q, r, calculate the determinant of a special matrix with three 2D points.
    # The sign, "-" or "+", determines the side, right or left, respectivly, on which the point r lies, when measured against
    # a directed vector from p to q.  Use Sarrus' Rule to calculate the determinant. (could also use the Numeric package...) 
    
    p,q,r = pts[0], pts[1], pts[2]  # for points p, q, and r

    # Sarrus' Rule (for computing determinants)...
    sum1 = q[0]*r[1] + p[0]*q[1] + r[0]*p[1]
    sum2 = q[0]*p[1] + r[0]*q[1] + p[0]*r[1]

    # if sum1 < sum2, then p,q,r form a right-hand turn...
    if sum1 < sum2: rightTurn = 1
    
    # else p,q,r do not form a left-hand turn
    else: rightTurn = 0
    
    return rightTurn


#-----------------------------------------------------------------------------

# SECTION 18: THE RANGE INDEX (RADIUS OF MINIMUM CIRCUMSCRIBED CIRCLE)...

# for every pair of points in the convex hull, calculate distance - this
# distance is the minimum diameter of a circle that circumscribes the shape

# use the points in the convex hull...
def Range(pntLst):

    dMax = 0    # maximum distance between 2 pts on the perimeter

    # for a point in the convex hull...
    for X1, Y1 in pntLst:

        # for another point in the convex hull...
        for X2,Y2 in pntLst:
     
            # distance between point 1 and point 2
            d = ((X1-X2)**2+(Y1-Y2)**2)**.5

            # if distance is greater than max distance
            if d > dMax:
                # set maximum distance
                dMax = d
                # keep XY coordinates of both points
                finalPtLst = [[X1,Y1],[X2,Y2]]

    # return maximum distance between 2 points
    return dMax

# ------------------------------------------------------------------
# DETERMINE IF A GIVEN LINE IS FULLY CONTAINED WITHIN A SHAPE...

def lineInPoly(line1,perimPntLst):

    poly_pntLst = []

    for ringLst in perimPntLst:
        poly_pntLst.extend(ringLst)


    # coordinates of line endpoints...
    X1,Y1 = float(line1[0][0]),float(line1[0][1])
    X2,Y2 = float(line1[1][0]),float(line1[1][1])

    # number of vertices in shape...
    numVertices = len(poly_pntLst)

    # initialize variables...
    intersect_cnt = lineInPoly = 0

    # for each position in vertex list...
    for pos in range(len(poly_pntLst)-1):

        # vertex coordinates...            
        x1,y1 = poly_pntLst[pos][0], poly_pntLst[pos][1]

        # if pos is not last item in list, get coordinates of next point...
        if pos < len(poly_pntLst)-2:
            x2,y2 = poly_pntLst[pos+1][0], poly_pntLst[pos+1][1]

        # if pos is last item in list, get coordinates of 1st point (final line segment)
        else:
            x2,y2 = poly_pntLst[0][0], poly_pntLst[0][1]
        
        # if both lines are the same, then test line is the same as the perimeter line segment...
        # and is inside the shape...
        if [x1,y1] in [[X1,Y1],[X2,Y2]] and [x2,y2] in [[X1,Y1],[X2,Y2]]:
            lineInPoly = 1          # no intersection
            break
        
        #---------------------------------------
        # equation for 1st line...

        # slope of line segment...
        if X1 == X2: M1 = 99999999999   # vertical line
        else: M1 = (Y2-Y1)/(X2-X1)      # calculate slope

        # intercept of segment
        B1 = Y1-(M1*X1)

        #---------------------------------------
        # equation of line 2...

        # slope of line segment
        if x1 == x2: m2 = 99999999999
        else: m2 = (y2-y1)/(x2-x1)

        # intercept of line segment...
        b2 = y1-m2*x1

        #---------------------------------------
        # test for intersection, if equal slopes, lines will never intersect so skip...
        
        if M1 != m2:       
            # calculate XY of intersection...                 
            X = (b2-B1)/(M1-m2)
            Y = M1*X + B1

            # distance between intersection and endpoint...
            D1 = ((X-X1)**2+(Y-Y1)**2)**.5      # end pnt 1
            D2 = ((X-X2)**2+(Y-Y2)**2)**.5      # end pnt 2
           
            # if almost no distance, intersection is an endpoint, do not count...
            if D1 < 1 or D2 < 1:
                continue

            # if intersection is not an endpoint, check if it is on the line segment...
            else:

                # sort X coordinates for each segment in ascending order...
                XLst,xLst = [X1,X2],[x1,x2]
                XLst.sort()
                xLst.sort()

                # if intersection X is in X range of both lines, then count it...
                if XLst[0] <= X <= XLst[1] and xLst[0] <= X <= xLst[1]:              
                    intersect_cnt += 1

    # if at least one intersection found, line is not fully contained within the shape...
    if intersect_cnt > 0:
        lineInPoly = 0
    # if no intersections found, make sure line is within shape (test line midpoint)...
    else:

        # calculate coordinates of test line midpoint...
        Xm = X1 + (X2-X1)/2
        Ym = Y1 + (Y2-Y1)/2

        # if line mid is in the shape, then entire line must be in shape...
        if pntInShp(perimPntLst,[Xm,Ym]) == 1:
            lineInPoly = 1
        
    # value = 0 indicates line not fully contained within shape
    # value = 1 indicates line fully contained within shape
    return lineInPoly


#---------------------------------------------------------------------------
# AVERAGE SHAPE TRAVERSAL DISTANCE

# DIKSTRA'S ALGORITHM IS USED TO CALCULATE THE MINIMUM DISTANCE FROM A GIVEN
# POINT ON THE PERIMETER OF THE SHAPE TO ALL OTHER POINTS ON THE PERIMETER -
# PATHS CANNOT GO OUTSIDE SHAPE. THE TRAVERSAL IS THE AVERAGE OF THE DISTANCES
# FOR ALL POINTS ON THE PERIMETER. PERIMETER POINTS SHOULD BE EVENLY SPACED.

def traversal_D(perimPntLst):

    shpCoordLst = []

    for ringLst in perimPntLst:
        shpCoordLst.extend(ringLst)

    # list of average distances for each perimeter point...
    avgDLst = []

    # for each point on perimeter...
    for Xs,Ys in shpCoordLst:

        # index location of current point in perimeter XY list...
        vLst = [shpCoordLst.index([Xs,Ys])]

        # list for distances from current point to all other points...

        # set initial minimum distance for each vertex to infinity...
        # so that any calculated distance will be smaller
        dLst = ["0"]*len(shpCoordLst)   

        # initialize sum distance variables. Iterations continue until
        # the sum stops changing...
        prevSumD = -1    # previous sum distance
        newSumD = 0      # current sum distance

        # list of points to which distance calculation is complete...
        pastLst = []

        # iterate until no further change occurs...
        while prevSumD != newSumD:

            # set previous sum distance to current...
            prevSumD = newSumD

            # reset current sum distance...
            newSumD = 0

            # current list of vertices - starting points
            curVLst = vLst[:]

            # vertices that have already been reached
            vLst = []

            # for each current vertex...
            for v in curVLst:

                # get coordinates of vertex
                Xc,Yc = shpCoordLst[v][0], shpCoordLst[v][1]

                # skip if this vertex if distance to intial point is already known...
                if [Xc,Yc] in pastLst:
                    continue

                # for each point in perimeter...
                for pos in range(len(shpCoordLst)-1):

                    # coordinates of point...
                    X, Y = shpCoordLst[pos][0], shpCoordLst[pos][1]

                    # skip if point is the same as initial point...
                    if [X,Y] == [Xs,Ys]: continue

                    # skip if point is same as current vertex...
                    if [X,Y] == [Xc,Yc]: continue

                    # euclidean distance between current vertex and current perimeter point
                    d = (((X-Xc)**2 + (Y-Yc)**2)**.5) + float(dLst[v])

                    # assume points are the same if distance between is very small...
                    if d < .1: continue

                    # if line is not fully contained within shape, skip point - it is an invalid path...
                    if lineInPoly([[Xc,Yc],[X,Y]],perimPntLst) == 0:
                        continue

                    # add point to list of "reached" vertices...
                    if pos not in vLst:
                        vLst.append(pos)

                    #---------------------------
                    # UPDATE DISTANCE LIST - distance list will have minimum distances calculated so far to a given perimeter point from the initial point...
                    
                    # get current distance value from distance list...
                    curDist = dLst.pop(pos)                   

                    # if previous distance is less than current distance, keep the previous distance
                    if curDist == "0":
                        curDist = d
                    elif curDist > d:
                        curDist = d

                    # insert distance into correct position in distance list...
                    dLst.insert(pos,curDist)
                    #---------------------------

                # add current vertex to past list - minimum distance to this vertex is not known...
                pastLst.append([Xc,Yc])

            # sum distances from initial point to each perimeter point...
            for d in dLst:
                newSumD += float(d)

        # average sum distances for each perimeter point...
        avgD = newSumD / len(dLst)

        # add average distance to list...
        avgDLst.append(avgD)

    #-----------------------------
    # AVERAGE DISTANCES FOR ALL PERIMETER POINTS - this is the shape's average traversal distance...
    
    avgD = 0
    for avg in avgDLst:
        avgD += avg

    avgD /= len(avgDLst)

    # return shape's average traversal distance...
    return avgD


def filter_features_by_area(input_features_path, output_features_path, area_threshold_km2=0):
    """
    Filters and retains features from the original shapefile if their area in km² is greater than the specified threshold.

    The area is calculated assuming the layer is in EPSG:3438 (feet).

    Parameters:
        input_features_path (str): Path to the original shapefile with the features.
        output_features_path (str): Path to save the filtered shapefile.
        area_threshold_km2 (float): Area threshold in square kilometers (default=0.036 km²).
    """
    # Conversion factor from square feet to square kilometers
    ft2_to_km2 = 0.000000092903

    # Load the original feature layer
    features_layer = QgsVectorLayer(input_features_path, "Original Features", "ogr")
    if not features_layer.isValid():
        raise ValueError(f"The feature layer could not be loaded from {input_features_path}.")

    # Crear una nueva capa filtrada incluyendo solo los features mayores al área mínima
    output_layer = QgsVectorLayer("Polygon?crs=EPSG:3438", "Filtered Features", "memory")
    output_provider = output_layer.dataProvider()

    # Copiar campos de la capa original
    output_provider.addAttributes(features_layer.fields())
    output_layer.updateFields()

    # Filtrar por área
    output_layer.startEditing()
    for feature in features_layer.getFeatures():
        geom = feature.geometry()
        if not geom.isGeosValid():
            print(f"Geometría inválida para el Feature ID: {feature.id()}")
            continue

        # Calcular el área en kilómetros cuadrados
        area_ft2 = geom.area()  # Área en pies cuadrados
        area_km2 = area_ft2 * ft2_to_km2  # Convertir a km²


        if area_km2 > area_threshold_km2:
            output_provider.addFeature(feature)

    output_layer.commitChanges()

    # Guardar la nueva capa en un archivo
    QgsVectorFileWriter.writeAsVectorFormat(output_layer, output_features_path, "UTF-8", output_layer.crs(), "ESRI Shapefile")


def generate_equidistant_points(polygon_geometry, num_points):
    """
    Genera puntos equidistantes sobre el perímetro de un polígono.

    Parámetros:
        polygon_geometry (QgsGeometry): Geometría del polígono.
        num_points (int): Número de puntos a generar.

    Retorna:
        list: Lista de QgsPointXY con los puntos equidistantes generados.
    """
    # Convertir el polígono en su perímetro como línea
    if polygon_geometry.isMultipart():
        rings = polygon_geometry.asMultiPolygon()
    else:
        rings = [polygon_geometry.asPolygon()]

    if not rings or not rings[0]:
        raise ValueError("No se pudieron extraer los anillos del polígono.")

    # Construir una geometría de línea a partir de los puntos del anillo exterior
    line_points = [QgsPointXY(point[0], point[1]) for ring in rings for point in ring[0]]
    perimeter = QgsGeometry.fromPolylineXY(line_points)

    if perimeter.isEmpty():
        raise ValueError("El perímetro del polígono está vacío.")

    # Longitud total del perímetro
    length = perimeter.length()

    # Distancia entre los puntos
    step = length / num_points

    # Generar puntos equidistantes
    points = []
    current_distance = 0

    while current_distance <= length:
        point = perimeter.interpolate(current_distance).asPoint()
        points.append(QgsPointXY(point.x(), point.y()))
        current_distance += step

    return points


def haversine(lat1, lon1, lat2, lon2):
    """
    Calcula la distancia en kilómetros entre dos puntos geográficos usando la fórmula del haversine.

    Parámetros:
        lat1, lon1: Coordenadas del primer punto (en grados).
        lat2, lon2: Coordenadas del segundo punto (en grados).

    Retorna:
        float: Distancia en kilómetros.
    """
    R = 6371.0  # Radio promedio de la Tierra en kilómetros
    dlat = radians(lat2 - lat1)
    dlon = radians(lon2 - lon1)
    a = sin(dlat / 2)**2 + cos(radians(lat1)) * cos(radians(lat2)) * sin(dlon / 2)**2
    c = 2 * atan2(sqrt(a), sqrt(1 - a))
    distance = R * c
    return distance


def calculate_min_distances_with_repeats(points_by_feature):
    """
    Calcula la distancia mínima entre puntos de diferentes features en kilómetros,
    permitiendo pares repetidos en ambas direcciones.

    Parámetros:
        points_by_feature (dict): Diccionario donde las claves son los IDs de los features
                                  y los valores son listas de puntos (QgsPointXY).

    Retorna:
        list: Lista de tuplas con información de distancias mínimas entre features.
    """
    min_distances = []

    # Iterar sobre cada par de features
    feature_ids = list(points_by_feature.keys())
    for source_id in feature_ids:
        for target_id in feature_ids:
            if source_id != target_id:  # Evitar comparar un feature consigo mismo
                min_distance = float("inf")
                closest_points = (None, None)

                # Comparar todos los puntos entre los dos features
                for source_point in points_by_feature[source_id]:
                    for target_point in points_by_feature[target_id]:
                        distance = haversine(
                            source_point.y(), source_point.x(),
                            target_point.y(), target_point.x()
                        )
                        # Actualizar si se encuentra una distancia menor
                        if distance < min_distance:
                            min_distance = distance
                            closest_points = (source_point, target_point)

                # Guardar la distancia mínima para este par de features
                min_distances.append({
                    "source_id": source_id,
                    "target_id": target_id,
                    "distance": min_distance,
                    "source_point": closest_points[0],
                    "target_point": closest_points[1],
                })

    return min_distances


def transform_to_crs(input_layer_path, output_layer_path, target_crs):
    """
    Transforma una capa a un CRS objetivo y guarda la capa transformada en un archivo.

    Parámetros:
        input_layer_path (str): Ruta al shapefile de entrada.
        output_layer_path (str): Ruta para guardar el shapefile transformado.
        target_crs (str): Código EPSG del CRS objetivo (e.g., "EPSG:4326").
    """
    layer = QgsVectorLayer(input_layer_path, "Layer", "ogr")
    if not layer.isValid():
        raise ValueError(f"No se pudo cargar la capa desde {input_layer_path}.")

    # Definir el nuevo CRS
    new_crs = QgsCoordinateReferenceSystem(target_crs)

    # Guardar la capa transformada
    QgsVectorFileWriter.writeAsVectorFormat(layer, output_layer_path, "UTF-8", new_crs, "ESRI Shapefile")


def filter_features_by_min_distances(input_distances_path, input_features_path, capital_path, output_features_path, distance_threshold_km=1.0):
    """
    Filtra iterativamente los polígonos comenzando por el que contiene la capital, incluyendo
    todos los polígonos con distancias mínimas menores al umbral, y expandiendo hacia afuera.

    Parámetros:
        input_distances_path (str): Ruta al shapefile con las distancias mínimas.
        input_features_path (str): Ruta al shapefile original de polígonos.
        capital_path (str): Ruta al shapefile de la capital.
        output_features_path (str): Ruta para guardar el shapefile filtrado.
        distance_threshold_km (float): Distancia máxima en kilómetros para incluir polígonos (default=1.0 km).
    """
    # Cargar capas
    distances_layer = QgsVectorLayer(input_distances_path, "Min Distances", "ogr")
    if not distances_layer.isValid():
        raise ValueError(f"No se pudo cargar la capa de distancias desde {input_distances_path}.")

    features_layer = QgsVectorLayer(input_features_path, "Polygons", "ogr")
    if not features_layer.isValid():
        raise ValueError(f"No se pudo cargar la capa de polígonos desde {input_features_path}.")

    capital_layer = QgsVectorLayer(capital_path, "Capital", "ogr")
    if not capital_layer.isValid():
        raise ValueError(f"No se pudo cargar la capa de la capital desde {capital_path}.")

    # Obtener la geometría de la capital
    capital_feature = next(capital_layer.getFeatures())
    capital_point = capital_feature.geometry().asPoint()

    # Encontrar el polígono que contiene la capital
    starting_feature_id = None
    for feature in features_layer.getFeatures():
        if feature.geometry().contains(QgsGeometry.fromPointXY(capital_point)):
            starting_feature_id = feature.id()
            break

    if starting_feature_id is None:
        return False


    # Inicializar conjuntos de features seleccionados y procesados
    selected_features = {starting_feature_id}
    processed_features = set()

    # Iterar para agregar features conectados por distancias menores al umbral
    while selected_features - processed_features:
        current_features = selected_features - processed_features
        for source_id in current_features:
            for feature in distances_layer.getFeatures():
                if feature["SourceFID"] == source_id:
                    target_id = feature["TargetFID"]
                    distance = feature["DistanceKM"]
                    if target_id not in selected_features and distance <= distance_threshold_km:
                        selected_features.add(target_id)
            processed_features.add(source_id)

    # Crear una nueva capa con los features seleccionados
    output_layer = QgsVectorLayer("Polygon?crs=EPSG:4326", f"Filtered Polygons", "memory")
    output_provider = output_layer.dataProvider()

    # Copiar campos de la capa original
    output_provider.addAttributes(features_layer.fields())
    output_layer.updateFields()

    # Agregar los features seleccionados
    output_layer.startEditing()
    for feature_id in selected_features:
        feature = features_layer.getFeature(feature_id)
        output_provider.addFeature(feature)
    output_layer.commitChanges()

    # Guardar la nueva capa en un archivo
    QgsVectorFileWriter.writeAsVectorFormat(output_layer, output_features_path, "UTF-8", output_layer.crs(), "ESRI Shapefile")

    return True


def find_and_expand_nearest_polygon_to_capital(input_distances_path, input_features_path, capital_path, equidistant_points_path, output_features_path, distance_threshold_km=1.0):
    """
    Encuentra el polígono más cercano a la capital utilizando puntos generados por generate_equidistant_points
    y expande iterativamente como en filter_features_by_min_distances.

    Parámetros:
        input_distances_path (str): Ruta al shapefile con las distancias mínimas.
        input_features_path (str): Ruta al shapefile original de polígonos.
        capital_path (str): Ruta al shapefile de la capital.
        equidistant_points_path (str): Ruta al shapefile con los puntos equidistantes generados.
        output_features_path (str): Ruta para guardar el shapefile filtrado.
        distance_threshold_km (float): Distancia máxima en kilómetros para expandir la selección (default=1.0 km).
    """
    # Cargar capas
    distances_layer = QgsVectorLayer(input_distances_path, "Min Distances", "ogr")
    if not distances_layer.isValid():
        raise ValueError(f"No se pudo cargar la capa de distancias desde {input_distances_path}.")

    features_layer = QgsVectorLayer(input_features_path, "Polygons", "ogr")
    if not features_layer.isValid():
        raise ValueError(f"No se pudo cargar la capa de polígonos desde {input_features_path}.")

    capital_layer = QgsVectorLayer(capital_path, "Capital", "ogr")
    if not capital_layer.isValid():
        raise ValueError(f"No se pudo cargar la capa de la capital desde {capital_path}.")

    equidistant_layer = QgsVectorLayer(equidistant_points_path, "Equidistant Points", "ogr")
    if not equidistant_layer.isValid():
        raise ValueError(f"No se pudo cargar la capa de puntos equidistantes desde {equidistant_points_path}.")

    # Obtener la geometría de la capital
    capital_feature = next(capital_layer.getFeatures())
    capital_point = capital_feature.geometry().asPoint()

    # Encontrar el polígono más cercano usando los puntos equidistantes
    nearest_polygon_id = None
    min_distance = float("inf")

    for point_feature in equidistant_layer.getFeatures():
        point_geom = point_feature.geometry()
        distance = capital_point.distance(point_geom.asPoint())

        if distance < min_distance:
            min_distance = distance
            nearest_polygon_id = point_feature["polygon_id"]  # Asumiendo que los puntos tienen un campo que referencia el polígono original

    if nearest_polygon_id is None:
        return False  # No se encontró un polígono cercano, se omite el municipio

    # Expansión iterativa desde el polígono más cercano
    selected_features = {nearest_polygon_id}
    processed_features = set()

    while selected_features - processed_features:
        current_features = selected_features - processed_features
        for source_id in current_features:
            for feature in distances_layer.getFeatures():
                if feature["SourceFID"] == source_id:
                    target_id = feature["TargetFID"]
                    distance = feature["DistanceKM"]
                    if target_id not in selected_features and distance <= distance_threshold_km:
                        selected_features.add(target_id)
            processed_features.add(source_id)

    # Crear una nueva capa con los features seleccionados
    output_layer = QgsVectorLayer("Polygon?crs=EPSG:4326", f"Filtered Polygons", "memory")
    output_provider = output_layer.dataProvider()

    # Copiar campos de la capa original
    output_provider.addAttributes(features_layer.fields())
    output_layer.updateFields()

    # Agregar los features seleccionados
    output_layer.startEditing()
    for feature_id in selected_features:
        feature = features_layer.getFeature(feature_id)
        output_provider.addFeature(feature)
    output_layer.commitChanges()

    # Guardar la nueva capa en un archivo
    QgsVectorFileWriter.writeAsVectorFormat(output_layer, output_features_path, "UTF-8", output_layer.crs(), "ESRI Shapefile")

    return True


def auto_accept_message_box():
    for widget in QApplication.instance().topLevelWidgets():
        if isinstance(widget, QMessageBox):
            widget.accept()  # Equivale a hacer click en "Yes"


#############################################################################
#############################################################################
#############################################################################

# MAIN
# First, we will start filtering the Municipality map.
# Path to original shapefile

# Ruta del archivo Excel
output_excel = "/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Metrics_24.xlsx"

# Crear el archivo Excel con encabezados si no existe
if not os.path.exists(output_excel):
    # Definir las columnas del Excel
    columns = ["ID", "Proximity", "nProximity", "Cohesion", "nCohesion", "Spin", "nSpin", 
               "Exchange", "nExchange", "Perimeter", "nPerimeter", "Dispers_", "nDispers_", "Range", "nRange", "Area_km2", "Perimeter_km"]
    
    # Crear un DataFrame vacío con las columnas
    df = pd.DataFrame(columns=columns)
    
    # Guardar el DataFrame en un archivo Excel
    df.to_excel(output_excel, index=False, engine='openpyxl')

# Obtener los valores de CD_MUN de las primeras municipalidades
municipalities = ['3140001', '3140100', '3140159', '3140209', '3140308', '3140407', '3140506', '3140530', '3140555', '3140605', '3140704', '3140803', '3140852', '3140902', '3141009', '3141108', '3141207', '3141306', '3141405', '3141504', '3141603', '3141702', '3141801', '3141900', '3142007', '3142106', '3142205', '3142254', '3142304', '3142403', '3142502', '3142601', '3142700', '3142809', '3142908', '3143005', '3143104', '3143153', '3143203', '3143302', '3143401', '3143450', '3143500', '3143609', '3143708', '3143807', '3143906', '3144003', '3144102', '3144201', '3144300', '3144359', '3144375', '3144409', '3144508', '3144607', '3144656', '3144672', '3144706', '3144805', '3144904', '3145000', '3145059', '3145109', '3145208', '3145307', '3145356', '3145372', '3145406', '3145455', '3145505', '3145604', '3145703', '3145802', '3145851', '3145877', '3145901', '3146008', '3146107', '3146206', '3146255', '3146305', '3146404', '3146503', '3146552', '3146602', '3146701', '3146750', '3146909', '3147006', '3147105', '3147204', '3147303', '3147402', '3147501', '3147600', '3147709', '3147808', '3147907', '3147956', '3148004', '3148103', '3148202', '3148301', '3148400', '3148509', '3148608', '3148707', '3148756', '3148806', '3148905', '3149002', '3149101', '3149150', '3149200', '3149309', '3149408', '3149507', '3149606', '3149705', '3149804', '3149903', '3149952', '3150000', '3150109', '3150158', '3150208', '3150307', '3150406', '3150505', '3150539', '3150570', '3150604', '3150703', '3150802', '3150901', '3151008', '3151107', '3151206', '3151305', '3151404', '3151503', '3151602', '3151701', '3151800', '3151909', '3152006', '3152105', '3152131', '3152170', '3152204', '3152303', '3152402', '3152501', '3152600', '3152709', '3152808', '3152907', '3153004', '3153103', '3153202', '3153301', '3153400', '3153509', '3153608', '3153707', '3153806', '3153905', '3154002', '3154101', '3154150', '3154200', '3154309', '3154408', '3154457', '3154507', '3154606', '3154705', '3154804', '3154903', '3155009', '3155108', '3155207', '3155306', '3155405', '3155504', '3155603', '3155702', '3155801', '3155900', '3156007', '3156106', '3156205', '3156304', '3156403', '3156452', '3156502', '3156601', '3156700', '3156809', '3156908', '3157005', '3157104', '3157203', '3157252', '3157278', '3157302', '3157336', '3157377', '3157401', '3157500', '3157609', '3157658', '3157708', '3157807', '3157906', '3158003', '3158102', '3158201', '3158300', '3158409', '3158508', '3158607', '3158706', '3158805', '3158904', '3158953', '3159001', '3159100', '3159209', '3159308', '3159357', '3159407', '3159506', '3159605', '3159704', '3159803', '3159902', '3160009', '3160108', '3160207', '3160306', '3160405', '3160454', '3160504', '3160603', '3160702', '3160801', '3160900', '3160959', '3161007', '3161056', '3161106', '3161205', '3161304', '3161403', '3161502', '3161601', '3161650', '3161700', '3161809', '3161908', '3162005', '3162104', '3162203', '3162252', '3162302', '3162401', '3162450', '3162500', '3162559', '3162575', '3162609', '3162658', '3162708', '3162807', '3162906', '3162922', '3162948', '3162955', '3163003', '3163102', '3163201', '3163300', '3163409', '3163508', '3163607', '3163706', '3163805', '3163904', '3164001', '3164100', '3164209', '3164308', '3164407', '3164431', '3164472', '3164506', '3164605', '3164704', '3164803', '3164902', '3165008', '3165107', '3165206', '3165305', '3165404', '3165503', '3165537', '3165552', '3165560', '3165578', '3165602', '3165701', '3165800', '3165909', '3166006', '3166105', '3166204', '3166303', '3166402', '3166501', '3166600', '3166709', '3166808', '3166907', '3166956', '3167004', '3167103', '3167202', '3167301', '3167400', '3167509', '3167608', '3167707', '3167806', '3167905', '3168002', '3168051', '3168101', '3168200', '3168309', '3168408', '3168507', '3168606', '3168705', '3168804', '3168903', '3169000', '3169059', '3169109', '3169208', '3169307', '3169356', '3169406', '3169505', '3169604', '3169703', '3169802', '3169901', '3170008', '3170057', '3170107', '3170206', '3170305', '3170404', '3170438', '3170479', '3170503', '3170529', '3170578', '3170602', '3170651', '3170701', '3170750', '3170800', '3170909', '3171006', '3171030', '3171071', '3171105', '3171154', '3171204', '3171303', '3171402', '3171501', '3171600', '3171709', '3171808', '3171907', '3172004', '3172103', '3172202', '3200102', '3200136', '3200169', '3200201', '3200300', '3200359', '3200409', '3200508', '3200607', '3200706', '3200805', '3200904', '3201001', '3201100', '3201159', '3201209', '3201308', '3201407', '3201506', '3201605', '3201704', '3201803', '3201902', '3202009', '3202108', '3202207', '3202256', '3202306', '3202405', '3202454', '3202504', '3202553', '3202603', '3202652', '3202702', '3202801', '3202900', '3203007', '3203056', '3203106', '3203130', '3203163', '3203205', '3203304', '3203320', '3203346', '3203353', '3203403', '3203502', '3203601', '3203700', '3203809', '3203908', '3204005', '3204054', '3204104', '3204203', '3204252', '3204302', '3204351', '3204401', '3204500', '3204559', '3204609', '3204658', '3204708', '3204807', '3204906', '3204955', '3205002', '3205010', '3205036', '3205069', '3205101', '3205150', '3205176', '3205200', '3205309', '3300100', '3300159', '3300209', '3300225', '3300233', '3300258', '3300308', '3300407', '3300456', '3300506', '3300605', '3300704', '3300803', '3300902', '3300936', '3300951', '3301009', '3301108', '3301157', '3301207', '3301306', '3301405', '3301504', '3301603', '3301702', '3301801', '3301850', '3301876', '3301900', '3302007', '3302056', '3302106', '3302205', '3302254', '3302270', '3302304', '3302403', '3302452', '3302502', '3302601', '3302700', '3302809', '3302858', '3302908', '3303005', '3303104', '3303203', '3303302', '3303401', '3303500', '3303609', '3303708', '3303807', '3303856', '3303906', '3303955', '3304003', '3304102', '3304110', '3304128', '3304144', '3304151', '3304201', '3304300', '3304409', '3304508', '3304524', '3304557', '3304607', '3304706', '3304755', '3304805', '3304904', '3305000', '3305109', '3305133', '3305158', '3305208', '3305307', '3305406', '3305505', '3305554', '3305604', '3305703', '3305752', '3305802', '3305901', '3306008', '3306107', '3306156', '3306206', '3306305', '3500105', '3500204', '3500303', '3500402', '3500501', '3500550', '3500600', '3500709', '3500758', '3500808', '3500907', '3501004', '3501103', '3501152', '3501202', '3501301', '3501400', '3501509', '3501608', '3501707', '3501806', '3501905', '3502002', '3502101', '3502200', '3502309', '3502408', '3502507', '3502606', '3502705', '3502754', '3502804', '3502903', '3503000', '3503109', '3503158', '3503208', '3503307', '3503356', '3503406', '3503505', '3503604', '3503703', '3503802', '3503901', '3503950', '3504008', '3504107', '3504206', '3504305', '3504404', '3504503', '3504602', '3504701', '3504800', '3504909', '3505005', '3505104', '3505203', '3505302', '3505351', '3505401', '3505500', '3505609', '3505708', '3505807', '3505906', '3506003', '3506102', '3506201', '3506300', '3506359', '3506409', '3506508', '3506607', '3506706', '3506805', '3506904', '3507001', '3507100', '3507159', '3507209', '3507308', '3507407', '3507456', '3507506', '3507605', '3507704', '3507753', '3507803', '3507902', '3508009', '3508108', '3508207', '3508306', '3508405', '3508504', '3508603', '3508702', '3508801', '3508900', '3509007', '3509106', '3509205', '3509254', '3509304', '3509403', '3509452', '3509502', '3509601', '3509700', '3509809', '3509908', '3509957', '3510005', '3510104', '3510153', '3510203', '3510302', '3510401', '3510500', '3510609', '3510708', '3510807', '3510906', '3511003', '3511102', '3511201', '3511300', '3511409', '3511508', '3511607', '3511706', '3511904', '3512001', '3512100', '3512209', '3512308', '3512407', '3512506', '3512605', '3512704', '3512803', '3512902', '3513009', '3513108', '3513207', '3513306', '3513405', '3513504', '3513603', '3513702', '3513801', '3513850', '3513900', '3514007', '3514106', '3514205', '3514304', '3514403', '3514502', '3514601', '3514700', '3514809', '3514908', '3514924', '3514957', '3515004', '3515103', '3515129', '3515152', '3515186', '3515194', '3515202', '3515301', '3515350', '3515400', '3515509', '3515608', '3515657', '3515707', '3515806', '3515905', '3516002', '3516101', '3516200', '3516309', '3516408', '3516507', '3516606', '3516705', '3516804', '3516853', '3516903', '3517000', '3517109', '3517208', '3517307', '3517406', '3517505', '3517604', '3517703', '3517802', '3517901', '3518008', '3518107', '3518206', '3518305', '3518404', '3518503', '3518602', '3518701', '3518800', '3518859', '3518909', '3519006', '3519055', '3519071', '3519105', '3519204', '3519253', '3519303', '3519402', '3519501', '3519600', '3519709', '3519808', '3519907', '3520004', '3520103', '3520202', '3520301', '3520400', '3520426', '3520442', '3520509', '3520608', '3520707', '3520806', '3520905', '3521002', '3521101', '3521150', '3521200', '3521309', '3521408', '3521507', '3521606', '3521705', '3521804', '3521903', '3522000', '3522109', '3522158', '3522208', '3522307', '3522406', '3522505', '3522604', '3522653', '3522703', '3522802', '3522901', '3523008', '3523107', '3523206', '3523305', '3523404', '3523503', '3523602', '3523701', '3523800', '3523909', '3524006', '3524105', '3524204', '3524303', '3524402', '3524501', '3524600', '3524709', '3524808', '3524907', '3525003', '3525102', '3525201', '3525300', '3525409', '3525508', '3525607', '3525706', '3525805', '3525854', '3525904', '3526001', '3526100', '3526209', '3526308', '3526407', '3526506', '3526605', '3526704', '3526803', '3526902', '3527009', '3527108', '3527207', '3527256', '3527306', '3527405', '3527504', '3527603', '3527702', '3527801', '3527900', '3528007', '3528106', '3528205', '3528304', '3528403', '3528502', '3528601', '3528700', '3528809', '3528858', '3528908', '3529005', '3529104', '3529203', '3529302', '3529401', '3529500', '3529609', '3529658', '3529708', '3529807', '3529906', '3530003', '3530102', '3530201', '3530300', '3530409', '3530508', '3530607', '3530706', '3530805', '3530904', '3531001', '3531100', '3531209', '3531308', '3531407', '3531506', '3531605', '3531704', '3531803', '3531902', '3532009', '3532058', '3532108', '3532157', '3532207', '3532306', '3532405', '3532504', '3532603', '3532702', '3532801', '3532827', '3532843', '3532868', '3532900', '3533007', '3533106', '3533205', '3533254', '3533304', '3533403', '3533502', '3533601', '3533700', '3533809', '3533908', '3534005', '3534104', '3534203', '3534302', '3534401', '3534500', '3534609', '3534708', '3534757', '3534807', '3534906', '3535002', '3535101', '3535200', '3535309', '3535408', '3535507', '3535606', '3535705', '3535804', '3535903', '3536000', '3536109', '3536208', '3536257', '3536307', '3536406', '3536505', '3536570', '3536604', '3536703', '3536802', '3536901', '3537008', '3537107', '3537156', '3537206', '3537305', '3537404', '3537503', '3537602', '3537701', '3537800', '3537909', '3538006', '3538105', '3538204', '3538303', '3538501', '3538600', '3538709', '3538808', '3538907', '3539004', '3539103', '3539202', '3539301', '3539400', '3539509', '3539608', '3539707', '3539806', '3539905', '3540002', '3540101', '3540200', '3540259', '3540309', '3540408', '3540507', '3540606', '3540705', '3540754', '3540804', '3540853', '3540903', '3541000', '3541059', '3541109', '3541208', '3541307', '3541406', '3541505', '3541604', '3541653', '3541703', '3541802', '3541901', '3542008', '3542107', '3542206', '3542305', '3542404', '3542503', '3542602', '3542701', '3542800', '3542909', '3543006', '3543105', '3543204', '3543238', '3543253', '3543303', '3543402', '3543501', '3543600', '3543709', '3543808', '3543907', '3544004', '3544103', '3544202', '3544251', '3544301', '3544400', '3544509', '3544608', '3544707', '3544806', '3544905', '3545001', '3545100', '3545159', '3545209', '3545308', '3545407', '3545506', '3545605', '3545704', '3545803', '3546009', '3546108', '3546207', '3546256', '3546306', '3546405', '3546504', '3546603', '3546702', '3546801', '3546900', '3547007', '3547106', '3547205', '3547304', '3547403', '3547502', '3547601', '3547650', '3547700', '3547809', '3547908', '3548005', '3548054', '3548104', '3548203', '3548302', '3548401', '3548500', '3548609', '3548708', '3548807', '3548906', '3549003', '3549102', '3549201', '3549250', '3549300', '3549409', '3549508', '3549607', '3549706', '3549805', '3549904', '3549953', '3550001', '3550100', '3550209', '3550308', '3550407', '3550506', '3550605', '3550704', '3550803', '3550902', '3551009', '3551108', '3551207', '3551306', '3551405', '3551504', '3551603', '3551702', '3551801', '3551900', '3552007', '3552106', '3552205', '3552304', '3552403', '3552502', '3552551', '3552601', '3552700', '3552809', '3552908', '3553005', '3553104', '3553203', '3553302', '3553401', '3553500', '3553609', '3553658', '3553708', '3553807', '3553856', '3553906', '3553955', '3554003', '3554102', '3554201', '3554300', '3554409', '3554508', '3554607', '3554656', '3554706', '3554755', '3554805', '3554904', '3554953', '3555000', '3555109', '3555208', '3555307', '3555356', '3555406', '3555505', '3555604', '3555703', '3555802', '3555901', '3556008', '3556107', '3556206', '3556305', '3556354', '3556404', '3556453', '3556503', '3556602', '3556701', '3556800', '3556909', '3556958', '3557006', '3557105', '3557154', '3557204', '3557303', '4100103', '4100202', '4100301', '4100400', '4100459', '4100509', '4100608', '4100707', '4100806', '4100905', '4101002', '4101051', '4101101', '4101150', '4101200', '4101309', '4101408', '4101507', '4101606', '4101655', '4101705', '4101804', '4101853', '4101903', '4102000', '4102109', '4102208', '4102307', '4102406', '4102505', '4102604', '4102703', '4102752', '4102802', '4102901', '4103008', '4103024', '4103040', '4103057', '4103107', '4103156', '4103206', '4103222', '4103305', '4103354', '4103370', '4103404', '4103453', '4103479', '4103503', '4103602', '4103701', '4103800', '4103909', '4103958', '4104006', '4104055', '4104105', '4104204', '4104253', '4104303', '4104402', '4104428', '4104451', '4104501', '4104600', '4104659', '4104709', '4104808', '4104907', '4105003', '4105102', '4105201', '4105300', '4105409', '4105508', '4105607', '4105706', '4105805', '4105904', '4106001', '4106100', '4106209', '4106308', '4106407', '4106456', '4106506', '4106555', '4106571', '4106605', '4106704', '4106803', '4106852', '4106902', '4107009', '4107108', '4107124', '4107157', '4107207', '4107256', '4107306', '4107405', '4107504', '4107520', '4107538', '4107546', '4107553', '4107603', '4107652', '4107702', '4107736', '4107751', '4107801', '4107850', '4107900', '4108007', '4108106', '4108205', '4108304', '4108320', '4108403', '4108452', '4108502', '4108551', '4108601', '4108650', '4108700', '4108809', '4108908', '4108957', '4109005', '4109104', '4109203', '4109302', '4109401', '4109500', '4109609', '4109658', '4109708', '4109757', '4109807', '4109906', '4110003', '4110052', '4110078', '4110102', '4110201', '4110300', '4110409', '4110508', '4110607', '4110656', '4110706', '4110805', '4110904', '4110953', '4111001', '4111100', '4111209', '4111258', '4111308', '4111407', '4111506', '4111555', '4111605', '4111704', '4111803', '4111902', '4112009', '4112108', '4112207', '4112306', '4112405', '4112504', '4112603', '4112702', '4112751', '4112801', '4112900', '4112959', '4113007', '4113106', '4113205', '4113254', '4113304', '4113403', '4113429', '4113452', '4113502', '4113601', '4113700', '4113734', '4113759', '4113809', '4113908', '4114005', '4114104', '4114203', '4114302', '4114351', '4114401', '4114500', '4114609', '4114708', '4114807', '4114906', '4115002', '4115101', '4115200', '4115309', '4115358', '4115408', '4115457', '4115507', '4115606', '4115705', '4115739', '4115754', '4115804', '4115853', '4115903', '4116000', '4116059', '4116109', '4116208', '4116307', '4116406', '4116505', '4116604', '4116703', '4116802', '4116901', '4116950', '4117008', '4117057', '4117107', '4117206', '4117214', '4117222', '4117255', '4117271', '4117297', '4117305', '4117404', '4117453', '4117503', '4117602', '4117701', '4117800', '4117909', '4118006', '4118105', '4118204', '4118303', '4118402', '4118451', '4118501', '4118600', '4118709', '4118808', '4118857', '4118907', '4119004', '4119103', '4119152', '4119202', '4119251', '4119301', '4119400', '4119509', '4119608', '4119657', '4119707', '4119806', '4119905', '4119954', '4120002', '4120101', '4120150', '4120200', '4120309', '4120333', '4120358', '4120408', '4120507', '4120606', '4120655', '4120705', '4120804', '4120853', '4120903', '4121000', '4121109', '4121208', '4121257', '4121307', '4121356', '4121406', '4121505', '4121604', '4121703', '4121752', '4121802', '4121901', '4122008', '4122107', '4122156', '4122172', '4122206', '4122305', '4122404', '4122503', '4122602', '4122651', '4122701', '4122800', '4122909', '4123006', '4123105', '4123204', '4123303', '4123402', '4123501', '4123600', '4123709', '4123808', '4123824', '4123857', '4123907', '4123956', '4124004', '4124020', '4124053', '4124103', '4124202', '4124301', '4124400', '4124509', '4124608', '4124707', '4124806', '4124905', '4125001', '4125100', '4125209', '4125308', '4125357', '4125407', '4125456', '4125506', '4125555', '4125605', '4125704', '4125753', '4125803', '4125902', '4126009', '4126108', '4126207', '4126256', '4126272', '4126306', '4126355', '4126405', '4126504', '4126603', '4126652', '4126678', '4126702', '4126801', '4126900', '4127007', '4127106', '4127205', '4127304', '4127403', '4127502', '4127601', '4127700', '4127809', '4127858', '4127882', '4127908', '4127957', '4127965', '4128005', '4128104', '4128203', '4128302', '4128401', '4128500', '4128534', '4128559', '4128609', '4128625', '4128633', '4128658', '4128708', '4128807', '4200051', '4200101', '4200200', '4200309', '4200408', '4200507', '4200556', '4200606', '4200705', '4200754', '4200804', '4200903', '4201000', '4201109', '4201208', '4201257', '4201273', '4201307', '4201406', '4201505', '4201604', '4201653', '4201703', '4201802', '4201901', '4201950', '4202008', '4202057', '4202073', '4202081', '4202099', '4202107', '4202131', '4202156', '4202206', '4202305', '4202404', '4202438', '4202453', '4202503', '4202537', '4202578', '4202602', '4202701', '4202800', '4202859', '4202875', '4202909', '4203006', '4203105', '4203154', '4203204', '4203253', '4203303', '4203402', '4203501', '4203600', '4203709', '4203808', '4203907', '4203956', '4204004', '4204103', '4204152', '4204178', '4204194', '4204202', '4204251', '4204301', '4204350', '4204400', '4204459', '4204509', '4204558', '4204608', '4204707', '4204756', '4204806', '4204905', '4205001', '4205100', '4205159', '4205175', '4205191', '4205209', '4205308', '4205357', '4205407', '4205431', '4205456', '4205506', '4205555', '4205605', '4205704', '4205803', '4205902', '4206009', '4206108', '4206207', '4206306', '4206405', '4206504', '4206603', '4206652', '4206702', '4206751', '4206801', '4206900', '4207007', '4207106', '4207205', '4207304', '4207403', '4207502', '4207577', '4207601', '4207650', '4207684', '4207700', '4207759', '4207809', '4207858', '4207908', '4208005', '4208104', '4208203', '4208302', '4208401', '4208450', '4208500', '4208609', '4208708', '4208807', '4208906', '4208955', '4209003', '4209102', '4209151', '4209177', '4209201', '4209300', '4209409', '4209458', '4209508', '4209607', '4209706', '4209805', '4209854', '4209904', '4210001', '4210035', '4210050', '4210100', '4210209', '4210308', '4210407', '4210506', '4210555', '4210605', '4210704', '4210803', '4210852', '4210902', '4211009', '4211058', '4211108', '4211207', '4211256', '4211306', '4211405', '4211454', '4211504', '4211603', '4211652', '4211702', '4211751', '4211801', '4211850', '4211876', '4211892', '4211900', '4212007', '4212056', '4212106', '4212205', '4212239', '4212254', '4212270', '4212304', '4212403', '4212502', '4212601', '4212650', '4212700', '4212809', '4212908', '4213005', '4213104', '4213153', '4213203', '4213302', '4213351', '4213401', '4213500', '4213609', '4213708', '4213807', '4213906', '4214003', '4214102', '4214151', '4214201', '4214300', '4214409', '4214508', '4214607', '4214706', '4214805', '4214904', '4215000', '4215059', '4215075', '4215109', '4215208', '4215307', '4215356', '4215406', '4215455', '4215505', '4215554', '4215604', '4215653', '4215679', '4215687', '4215695', '4215703', '4215752', '4215802', '4215901', '4216008', '4216057', '4216107', '4216206', '4216255', '4216305', '4216354', '4216404', '4216503', '4216602', '4216701', '4216800', '4216909', '4217006', '4217105', '4217154', '4217204', '4217253', '4217303', '4217402', '4217501', '4217550', '4217600', '4217709', '4217758', '4217808', '4217907', '4217956', '4218004', '4218103', '4218202', '4218251', '4218301', '4218350', '4218400', '4218509', '4218608', '4218707', '4218756', '4218806', '4218855', '4218905', '4218954', '4219002', '4219101', '4219150', '4219176', '4219200', '4219309', '4219358', '4219408', '4219507', '4219606', '4219705', '4219853', '4220000', '4300001', '4300002', '4300034', '4300059', '4300109', '4300208', '4300307', '4300406', '4300455', '4300471', '4300505', '4300554', '4300570', '4300604', '4300638', '4300646', '4300661', '4300703', '4300802', '4300851', '4300877', '4300901', '4301008', '4301057', '4301073', '4301107', '4301206', '4301305', '4301404', '4301503', '4301552', '4301602', '4301636', '4301651', '4301701', '4301750', '4301800', '4301859', '4301875', '4301909', '4301925', '4301958', '4302006', '4302055', '4302105', '4302154', '4302204', '4302220', '4302238', '4302253', '4302303', '4302352', '4302378', '4302402', '4302451', '4302501', '4302584', '4302600', '4302659', '4302709', '4302808', '4302907', '4303004', '4303103', '4303202', '4303301', '4303400', '4303509', '4303558', '4303608', '4303673', '4303707', '4303806', '4303905', '4304002', '4304101', '4304200', '4304309', '4304358', '4304408', '4304507', '4304606', '4304614', '4304622', '4304630', '4304655', '4304663', '4304671', '4304689', '4304697', '4304705', '4304713', '4304804', '4304853', '4304903', '4304952', '4305009', '4305108', '4305116', '4305124', '4305132', '4305157', '4305173', '4305207', '4305306', '4305355', '4305371', '4305405', '4305439', '4305447', '4305454', '4305504', '4305587', '4305603', '4305702', '4305801', '4305835', '4305850', '4305871', '4305900', '4305934', '4305959', '4305975', '4306007', '4306056', '4306072', '4306106', '4306130', '4306205', '4306304', '4306320', '4306353', '4306379', '4306403', '4306429', '4306452', '4306502', '4306551', '4306601', '4306700', '4306734', '4306759', '4306767', '4306809', '4306908', '4306924', '4306932', '4306957', '4306973', '4307005', '4307054', '4307104', '4307203', '4307302', '4307401', '4307450', '4307500', '4307559', '4307609', '4307708', '4307807', '4307815', '4307831', '4307864', '4307906', '4308003', '4308052', '4308078', '4308102', '4308201', '4308250', '4308300', '4308409', '4308433', '4308458', '4308508', '4308607', '4308656', '4308706', '4308805', '4308854', '4308904', '4309001', '4309050', '4309100', '4309126', '4309159', '4309209', '4309258', '4309308', '4309407', '4309506', '4309555', '4309571', '4309605', '4309654', '4309704', '4309753', '4309803', '4309902', '4309951', '4310009', '4310108', '4310207', '4310306', '4310330', '4310363', '4310405', '4310413', '4310439', '4310462', '4310504', '4310538', '4310553', '4310579', '4310603', '4310652', '4310702', '4310751', '4310801', '4310850', '4310876', '4310900', '4311007', '4311106', '4311122', '4311130', '4311155', '4311205', '4311239', '4311254', '4311270', '4311304', '4311403', '4311429', '4311502', '4311601', '4311627', '4311643', '4311700', '4311718', '4311734', '4311759', '4311775', '4311791', '4311809', '4311908', '4311981', '4312005', '4312054', '4312104', '4312138', '4312153', '4312179', '4312203', '4312252', '4312302', '4312351', '4312377', '4312385', '4312401', '4312427', '4312443', '4312450', '4312476', '4312500', '4312609', '4312617', '4312625', '4312658', '4312674', '4312708', '4312757', '4312807', '4312906', '4312955', '4313003', '4313011', '4313037', '4313060', '4313086', '4313102', '4313201', '4313300', '4313334', '4313359', '4313375', '4313391', '4313409', '4313425', '4313441', '4313466', '4313490', '4313508', '4313607', '4313656', '4313706', '4313805', '4313904', '4313953', '4314001', '4314027', '4314035', '4314050', '4314068', '4314076', '4314100', '4314134', '4314159', '4314175', '4314209', '4314308', '4314407', '4314423', '4314456', '4314464', '4314472', '4314498', '4314506', '4314548', '4314555', '4314605', '4314704', '4314753', '4314779', '4314787', '4314803', '4314902', '4315008', '4315057', '4315073', '4315107', '4315131', '4315149', '4315156', '4315172', '4315206', '4315305', '4315313', '4315321', '4315354', '4315404', '4315453', '4315503', '4315552', '4315602', '4315701', '4315750', '4315800', '4315909', '4315958', '4316006', '4316105', '4316204', '4316303', '4316402', '4316428', '4316436', '4316451', '4316477', '4316501', '4316600', '4316709', '4316733', '4316758', '4316808', '4316907', '4316956', '4316972', '4317004', '4317103', '4317202', '4317251', '4317301', '4317400', '4317509', '4317558', '4317608', '4317707', '4317756', '4317806', '4317905', '4317954', '4318002', '4318051', '4318101', '4318200', '4318309', '4318408', '4318424', '4318432', '4318440', '4318457', '4318465', '4318481', '4318499', '4318507', '4318606', '4318614', '4318622', '4318705', '4318804', '4318903', '4319000', '4319109', '4319125', '4319158', '4319208', '4319307', '4319356', '4319364', '4319372', '4319406', '4319505', '4319604', '4319703', '4319711', '4319737', '4319752', '4319802', '4319901', '4320008', '4320107', '4320206', '4320230', '4320263', '4320305', '4320321', '4320354', '4320404', '4320453', '4320503', '4320552', '4320578', '4320602', '4320651', '4320677', '4320701', '4320800', '4320859', '4320909', '4321006', '4321105', '4321204', '4321303', '4321329', '4321352', '4321402', '4321436', '4321451', '4321469', '4321477', '4321493', '4321501', '4321600', '4321626', '4321634', '4321667', '4321709', '4321808', '4321832', '4321857', '4321907', '4321956', '4322004', '4322103', '4322152', '4322186', '4322202', '4322251', '4322301', '4322327', '4322343', '4322350', '4322376', '4322400', '4322509', '4322525', '4322533', '4322541', '4322558', '4322608', '4322707', '4322806', '4322855', '4322905', '4323002', '4323101', '4323200', '4323309', '4323358', '4323408', '4323457', '4323507', '4323606', '4323705', '4323754', '4323770', '4323804', '5000203', '5000252', '5000609', '5000708', '5000807', '5000856', '5000906', '5001003', '5001102', '5001243', '5001508', '5001904', '5002001', '5002100', '5002159', '5002209', '5002308', '5002407', '5002605', '5002704', '5002803', '5002902', '5002951', '5003108', '5003157', '5003207', '5003256', '5003306', '5003454', '5003488', '5003504', '5003702', '5003751', '5003801', '5003900', '5004007', '5004106', '5004304', '5004403', '5004502', '5004601', '5004700', '5004809', '5004908', '5005004', '5005103', '5005152', '5005202', '5005251', '5005400', '5005608', '5005681', '5005707', '5005806', '5006002', '5006200', '5006259', '5006275', '5006309', '5006358', '5006408', '5006606', '5006903', '5007109', '5007208', '5007307', '5007406', '5007505', '5007554', '5007695', '5007703', '5007802', '5007901', '5007935', '5007950', '5007976', '5008008', '5008305', '5008404', '5100102', '5100201', '5100250', '5100300', '5100359', '5100409', '5100508', '5100607', '5100805', '5101001', '5101209', '5101258', '5101308', '5101407', '5101605', '5101704', '5101803', '5101852', '5101902', '5102504', '5102603', '5102637', '5102678', '5102686', '5102694', '5102702', '5102793', '5102850', '5103007', '5103056', '5103106', '5103205', '5103254', '5103304', '5103353', '5103361', '5103379', '5103403', '5103437', '5103452', '5103502', '5103601', '5103700', '5103809', '5103858', '5103908', '5103957', '5104104', '5104203', '5104500', '5104526', '5104542', '5104559', '5104609', '5104807', '5104906', '5105002', '5105101', '5105150', '5105176', '5105200', '5105234', '5105259', '5105309', '5105507', '5105580', '5105606', '5105622', '5105903', '5106000', '5106109', '5106158', '5106174', '5106182', '5106190', '5106208', '5106216', '5106224', '5106232', '5106240', '5106257', '5106265', '5106273', '5106281', '5106299', '5106307', '5106315', '5106372', '5106422', '5106455', '5106505', '5106653', '5106703', '5106752', '5106778', '5106802', '5106828', '5106851', '5107008', '5107040', '5107065', '5107107', '5107156', '5107180', '5107198', '5107206', '5107248', '5107263', '5107297', '5107305', '5107354', '5107404', '5107578', '5107602', '5107701', '5107743', '5107750', '5107768', '5107776', '5107792', '5107800', '5107859', '5107875', '5107883', '5107909', '5107925', '5107941', '5107958', '5108006', '5108055', '5108105', '5108204', '5108303', '5108352', '5108402', '5108501', '5108600', '5108808', '5108857', '5108907', '5108956', '5200050', '5200100', '5200134', '5200159', '5200175', '5200209', '5200258', '5200308', '5200506', '5200555', '5200605', '5200803', '5200829', '5200852', '5200902', '5201108', '5201207', '5201306', '5201405', '5201454', '5201504', '5201603', '5201702', '5201801', '5202155', '5202353', '5202502', '5202601', '5202809', '5203104', '5203203', '5203302', '5203401', '5203500', '5203559', '5203575', '5203609', '5203807', '5203906', '5203939', '5203962', '5204003', '5204102', '5204201', '5204250', '5204300', '5204409', '5204508', '5204557', '5204607', '5204656', '5204706', '5204805', '5204854', '5204904', '5204953', '5205000', '5205059', '5205109', '5205208', '5205307', '5205406', '5205455', '5205471', '5205497', '5205513', '5205521', '5205703', '5205802', '5205901', '5206206', '5206305', '5206404', '5206503', '5206602', '5206701', '5206800', '5206909', '5207105', '5207253', '5207352', '5207402', '5207501', '5207535', '5207600', '5207808', '5207907', '5208004', '5208103', '5208152', '5208301', '5208400', '5208509', '5208608', '5208707', '5208806', '5208905', '5209101', '5209150', '5209200', '5209291', '5209408', '5209457', '5209606', '5209705', '5209804', '5209903', '5209937', '5209952', '5210000', '5210109', '5210158', '5210208', '5210307', '5210406', '5210562', '5210604', '5210802', '5210901', '5211008', '5211206', '5211305', '5211404', '5211503', '5211602', '5211701', '5211800', '5211909', '5212006', '5212055', '5212105', '5212204', '5212253', '5212303', '5212501', '5212600', '5212709', '5212808', '5212907', '5212956', '5213004', '5213053', '5213087', '5213103', '5213400', '5213509', '5213707', '5213756', '5213772', '5213806', '5213855', '5213905', '5214002', '5214051', '5214101', '5214408', '5214507', '5214606', '5214705', '5214804', '5214838', '5214861', '5214879', '5214903', '5215009', '5215207', '5215231', '5215256', '5215306', '5215405', '5215504', '5215603', '5215652', '5215702', '5215801', '5215900', '5216007', '5216304', '5216403', '5216452', '5216809', '5216908', '5217104', '5217203', '5217302', '5217401', '5217609', '5217708', '5218003', '5218052', '5218102', '5218300', '5218391', '5218508', '5218607', '5218706', '5218789', '5218805', '5218904', '5219001', '5219100', '5219209', '5219258', '5219308', '5219357', '5219407', '5219456', '5219506', '5219605', '5219704', '5219712', '5219738', '5219753', '5219803', '5219902', '5220009', '5220058', '5220108', '5220157', '5220207', '5220264', '5220280', '5220405', '5220454', '5220504', '5220603', '5220686', '5220702', '5221007', '5221080', '5221197', '5221304', '5221403', '5221452', '5221502', '5221551', '5221577', '5221601', '5221700', '5221809', '5221858', '5221908', '5222005', '5222054', '5222203', '5222302', '5300108']

# Cargar la capa vectorial
input_path = f'/Users/maurocastiella/Desktop/CAF/Planning/Mapas/BR_Municipios_2023/BR_Municipios_2023.shp'
layer = QgsVectorLayer(input_path, "Municipios Filtrados", "ogr")

if not layer.isValid():
    raise ValueError("Error: No se pudo cargar la capa de municipios.")

# Extraer las primeras 3 municipalidades de la columna 'CD_MUN'
for feature in layer.getFeatures():
    municipalities.append(feature['CD_MUN'])
    if len(municipalities) == 500:  # Parar después de obtener 3 IDs
        break

for mun in municipalities:

# Loop para procesar municipios y guardar métricas

    input_path = f'/Users/maurocastiella/Desktop/CAF/Planning/Mapas/BR_Municipios_2023/BR_Municipios_2023.shp'

    # Cargar la capa vectorial
    layer = QgsVectorLayer(input_path, "Municipios Filtrados", "ogr")

    raster_path = f'/Users/maurocastiella/Desktop/CAF/Planning/Mapas/brasil_coverage_2024.tif'

    # Load the raster
    raster_layer = QgsRasterLayer(raster_path, "Brasil Urban Coverage")
    if not raster_layer.isValid():
        print("Error: Could not load the raster file.")

    if not layer.isValid():
        print("Error: Could not load layer.")


    # Filter the capital with the code in the CD_MUN column 
    codigo_municipio = f'{mun}'
    expression = f'"CD_MUN" = \'{codigo_municipio}\''

    # Create a list with selected entities
    selected_features = layer.getFeatures(QgsFeatureRequest().setFilterExpression(expression))
    features_list = [feature for feature in selected_features]

    if features_list:
        # Crear una capa temporal para el municipio seleccionado
        temp_layer = QgsVectorLayer("Polygon?crs=EPSG:4326", "Municipio_Seleccionado", "memory")  # Initial CRS (EPSG:4326)
        temp_layer_data = temp_layer.dataProvider()
        temp_layer_data.addAttributes(layer.fields())  # Copiar campos
        temp_layer.updateFields()
        temp_layer_data.addFeatures(features_list)  # Copiar entidad filtrada

        # Define the destination CRS (EPSG:3438) in order to replicate Parent et al.'s metrics.
        target_crs = QgsCoordinateReferenceSystem("EPSG:3438")
        temp_layer.setCrs(QgsCoordinateReferenceSystem("EPSG:4326"))  # Current CRS of temporal layer
        transform = QgsCoordinateTransform(temp_layer.crs(), target_crs, QgsProject.instance())

        # Transform the geometries to the new CRS
        for feature in temp_layer.getFeatures():
            geometry = feature.geometry()
            geometry.transform(transform)
            feature.setGeometry(geometry)

        # Save the transformed layer as a new shapefile
        output_path = f"/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Mun_{mun}.shp"
        QgsVectorFileWriter.writeAsVectorFormat(
            temp_layer,
            output_path,
            "UTF-8",
            target_crs,
            driverName="ESRI Shapefile"
        )

    else:
        print(f"The municipality with CD_MUN was not found = {codigo_municipio}.")


    # Now, we are going to filter the Capital Cities of every Municipality
    # Path to original shapefile
    input_path = f'/Users/maurocastiella/Desktop/CAF/Planning/Mapas/Capitales/Capitales.shp'

    # Load the vector layer
    layer = QgsVectorLayer(input_path, "Capitales", "ogr")

    if not layer.isValid():
        print("Error: No se pudo cargar la capa.")


    # Filter the capital with the code in the GEOCODIGO_ column
    codigo_capital = mun
    expression = f'"GEOCODIGO_" = \'{codigo_capital}\''

    # Create a list with selected entities
    selected_features = layer.getFeatures(QgsFeatureRequest().setFilterExpression(expression))
    features_list = [feature for feature in selected_features]

    if features_list:
        # Create a temporary layer for the selected capital
        temp_layer = QgsVectorLayer("Point?crs=EPSG:4326", "Capital_Seleccionada", "memory")  # Initial CRS (EPSG:4326)
        temp_layer_data = temp_layer.dataProvider()
        temp_layer_data.addAttributes(layer.fields())  # Copiar campos
        temp_layer.updateFields()
        temp_layer_data.addFeatures(features_list)  # Copiar entidad filtrada

        # Define the destination CRS (EPSG:3438)
        target_crs = QgsCoordinateReferenceSystem("EPSG:3438")
        temp_layer.setCrs(QgsCoordinateReferenceSystem("EPSG:4326"))  # CRS actual de la capa temporal
        transform = QgsCoordinateTransform(temp_layer.crs(), target_crs, QgsProject.instance())

        # Transform the geometries to the new CRS
        for feature in temp_layer.getFeatures():
            geometry = feature.geometry()
            geometry.transform(transform)
            feature.setGeometry(geometry)

        # Save the transformed layer as a new shapefile
        output_path = f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Capital_{mun}.shp'
        QgsVectorFileWriter.writeAsVectorFormat(
            temp_layer,
            output_path,
            "UTF-8",
            target_crs,
            driverName="ESRI Shapefile"
        )

    else:
        print(f"The capital was not found with GEOCODIGO_ = {codigo_capital}.")

    municipio_shapefile = f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Mun_{mun}.shp'

    # Load the municipality shapefile
    vector_layer = QgsVectorLayer(municipio_shapefile, "Municipio Recorte", "ogr")
    if not vector_layer.isValid():
        print("Error: The municipality shapefile could not be loaded.")

    # Define output path for the cut raster
    output_raster_path = f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Raster_{mun}.tif'

    # Configurar el procesamiento
    processing_feedback = QgsProcessingFeedback()

    # Cut the raster for our municipality
    params = {
        'INPUT': raster_path,
        'MASK': municipio_shapefile,
        'TARGET_CRS': None,  # Utilizar el CRS original del ráster
        'NODATA': -9999,     # Valor para nodata, ajusta según tu ráster si es necesario
        'ALPHA_BAND': False,
        'CROP_TO_CUTLINE': True,  # Recortar el ráster a los bordes de la máscara
        'KEEP_RESOLUTION': True,  # Mantener la resolución original del ráster
        'OUTPUT': output_raster_path
    }

    result = processing.run('gdal:cliprasterbymasklayer', params, feedback=processing_feedback)


    # Routes
    input_raster = f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Raster_{mun}.tif'
    style_path = f'/Users/maurocastiella/Desktop/CAF/Planning/Mapas/ESTILO_QGIS_COL9.qml'
    output_filtered_raster = f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Raster_Urban_Area_{mun}.tif'

    # Load the raster
    raster_layer = QgsRasterLayer(input_raster, "Raster Recortado")
    if not raster_layer.isValid():
        print("Error: Could not load the raster file.")


    # Use the raster calculator to keep only class 24 (Urban Area)
    # Expression: Keep 24, assign nodata to the rest
    calc_expression = f"((A == 24) * 24) + ((A != 24) * -9999)"  # Mantener 24, nodata en el resto

    params_calc = {
        'INPUT_A': input_raster,
        'BAND_A': 1,  # Usamos la banda 1 del ráster
        'FORMULA': calc_expression,
        'NO_DATA': -9999,  # Valor nodata
        'RTYPE': 5,  # Entero sin signo
        'OUTPUT': 'TEMPORARY_OUTPUT'
    }

    calc_result = processing.run("gdal:rastercalculator", params_calc)
    filtered_raster = calc_result['OUTPUT']

    # Apply style from QML file
    raster_layer = QgsRasterLayer(filtered_raster, f"Raster Urban Area")
    if not raster_layer.isValid():
        print("Error: Could not load filtered raster.")


    # Apply the style
    raster_layer.loadNamedStyle(style_path)
    raster_layer.triggerRepaint()

    # Add the layer to the project
    QgsProject.instance().addMapLayer(raster_layer)

    # Save the filtered raster with compression
    params_translate = {
        'INPUT': filtered_raster,
        'OUTPUT': output_filtered_raster,
        'OPTIONS': 'COMPRESS=LZW',  # Compresión LZW
        'DATA_TYPE': 5,  # Entero sin signo
    }

    processing.run("gdal:translate", params_translate)

    # Routes
    input_raster = f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Raster_Urban_Area_{mun}.tif'
    output_vector = f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}_temp.shp'

    # We will polygonize the raster files
    params_polygonize = {
        'INPUT': input_raster,
        'BAND': 1,  # Usamos la banda 1 del ráster
        'FIELD': 'value',  # Nombre del campo que contendrá los valores del ráster
        'EIGHT_CONNECTEDNESS': False,  # Usa conectividad de 4 direcciones (False) o 8 direcciones (True)
        'OUTPUT': output_vector
    }

    result = processing.run("gdal:polygonize", params_polygonize)

    # Load the resulting shapefile
    polygon_layer = QgsVectorLayer(output_vector, f"Urban Area Polygons", "ogr")
    if not polygon_layer.isValid():
        print("Error: Could not load polygon layer.")


    # Add the layer to the project
    QgsProject.instance().addMapLayer(polygon_layer)

    # Ruta del shapefile original
    input_shp = f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}_temp.shp'

    # Ruta temporal para guardar el shapefile transformado
    temp_shp = f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}_temp2.shp'

    # Cargar la capa original
    layer = QgsVectorLayer(input_shp, "Curitiba", "ogr")

    # Verificar que la capa se haya cargado correctamente
    if not layer.isValid():
        raise ValueError("No se pudo cargar la capa.")

    # Definir el nuevo CRS
    new_crs = QgsCoordinateReferenceSystem("EPSG:3438")

    # Guardar la capa con el nuevo CRS en un archivo temporal
    QgsVectorFileWriter.writeAsVectorFormat(layer, temp_shp, "UTF-8", new_crs, "ESRI Shapefile")



    # --- Configuración de entrada ---
    input_features_path = f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}_temp2.shp'
    output_features_path = f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}_temp3.shp'

    # Ejecutar la función con un umbral de área de 0.036 km²
    filter_features_by_area(input_features_path, output_features_path, area_threshold_km2=0)


    # Ruta del shapefile original
    input_shp = f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}_temp3.shp'

    # Ruta temporal para guardar el shapefile transformado
    temp_shp = f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}.shp'

    # Cargar la capa original
    layer = QgsVectorLayer(input_shp, "Curitiba", "ogr")

    # Verificar que la capa se haya cargado correctamente
    if not layer.isValid():
        raise ValueError("No se pudo cargar la capa.")

    # Definir el nuevo CRS
    new_crs = QgsCoordinateReferenceSystem("EPSG:4326")

    # Guardar la capa con el nuevo CRS en un archivo temporal
    QgsVectorFileWriter.writeAsVectorFormat(layer, temp_shp, "UTF-8", new_crs, "ESRI Shapefile")


    # --- Configuración de entrada ---
    input_layer_path = f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}.shp'
    output_points_path = f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Generated_points_{mun}.shp'
    output_distances_path = f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Min_Distances_KM_{mun}.shp'
    num_points = 80

    # Cargar la capa de polígonos
    layer = QgsVectorLayer(input_layer_path, "Polygons", "ogr")
    if not layer.isValid():
        raise ValueError("No se pudo cargar la capa de entrada.")

    # Generar puntos equidistantes y guardarlos
    all_points = {}
    point_layer = QgsVectorLayer("Point?crs=EPSG:4326", "Generated Points", "memory")
    provider = point_layer.dataProvider()

    provider.addAttributes([QgsField("polygon_id", QVariant.Int)])
    point_layer.updateFields()

    for feature in layer.getFeatures():
        geom = feature.geometry()
        polygon_id = feature.id()
        try:
            points = generate_equidistant_points(geom, num_points=num_points)
            all_points[polygon_id] = points
            for point in points:
                new_feature = QgsFeature()
                new_feature.setGeometry(QgsGeometry.fromPointXY(point))
                new_feature.setAttributes([polygon_id])
                provider.addFeature(new_feature)
        except Exception as e:
            print(f"Error at processing polygon with ID {polygon_id}: {e}")

    # Guardar puntos generados
    QgsVectorFileWriter.writeAsVectorFormat(point_layer, output_points_path, "UTF-8", layer.crs(), "ESRI Shapefile")

    # Calcular distancias mínimas y guardarlas
    min_distances = calculate_min_distances_with_repeats(all_points)
    line_layer = QgsVectorLayer("LineString?crs=EPSG:4326", "Min Distances", "memory")
    line_provider = line_layer.dataProvider()

    line_provider.addAttributes([
        QgsField("SourceFID", QVariant.Int),
        QgsField("TargetFID", QVariant.Int),
        QgsField("DistanceKM", QVariant.Double)
    ])
    line_layer.updateFields()

    for data in min_distances:
        line_geom = QgsGeometry.fromPolylineXY([data["source_point"], data["target_point"]])
        line_feature = QgsFeature()
        line_feature.setGeometry(line_geom)
        line_feature.setAttributes([data["source_id"], data["target_id"], data["distance"]])
        line_provider.addFeature(line_feature)

    QgsVectorFileWriter.writeAsVectorFormat(line_layer, output_distances_path, "UTF-8", line_layer.crs(), "ESRI Shapefile")


    # --- Configuración de entrada ---
    input_features_path = f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}.shp'
    capital_path = f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Capital_{mun}.shp'
    input_distances_path = f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Min_Distances_KM_{mun}.shp'
    output_features_path = f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Filtered_Polygons_{mun}.shp'

    # Transformar las capas al mismo CRS (EPSG:4326)
    features_transformed_path = f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}_4326.shp'
    capital_transformed_path = f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Capital_{mun}_4326.shp'
    distances_transformed_path = f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Min_Distances_KM_{mun}_4326.shp'

    transform_to_crs(input_features_path, features_transformed_path, "EPSG:4326")
    transform_to_crs(capital_path, capital_transformed_path, "EPSG:4326")
    transform_to_crs(input_distances_path, distances_transformed_path, "EPSG:4326")

    # Ejecutar la función con las capas transformadas
    result2 = filter_features_by_min_distances(distances_transformed_path, features_transformed_path, capital_transformed_path, output_features_path, distance_threshold_km=1.0)

    if not result2:
        print(f"La capital de {mun} no se encuentra en ningún polígono. Buscando el más cercano y expandiendo...")
        success = find_and_expand_nearest_polygon_to_capital(distances_transformed_path, features_transformed_path, capital_transformed_path, output_points_path, output_features_path, distance_threshold_km=1.0)
        if not success:
            print(f"No se pudo encontrar un polígono adecuado para {mun}. Municipio omitido.")
            continue
            

    # Ruta del shapefile original
    input_shp = f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Filtered_Polygons_{mun}.shp'

    # Ruta temporal para guardar el shapefile transformado
    temp_shp = f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Filtered_Polygons_{mun}_temp.shp'

    # Cargar la capa original
    layer = QgsVectorLayer(input_shp, "Curitiba", "ogr")

    # Verificar que la capa se haya cargado correctamente
    if not layer.isValid():
        raise ValueError("No se pudo cargar la capa.")

    # Definir el nuevo CRS
    new_crs = QgsCoordinateReferenceSystem("EPSG:3438")

    # Guardar la capa con el nuevo CRS en un archivo temporal
    QgsVectorFileWriter.writeAsVectorFormat(layer, temp_shp, "UTF-8", new_crs, "ESRI Shapefile")

    # Ruta al shapefile de entrada
    input_layer_path = f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Filtered_Polygons_{mun}_temp.shp'

    # Cargar la capa desde el shapefile
    input_layer = QgsVectorLayer(input_layer_path, f'Filtered Polygons', 'ogr')

    # Verificar si la capa es válida
    if not input_layer.isValid():
        print(f"Error: No se pudo cargar la capa desde {input_layer_path}.")
    else:
        # Agregar la capa al proyecto antes de continuar
        QgsProject.instance().addMapLayer(input_layer)

        # **Interrupción manual o espera (si fuera necesario)**:
        # Esto asegura que QGIS termine de cargar la capa antes de proceder.
        app = QApplication.instance()
        app.processEvents()
        # Acceder al plugin Concave Hull
        concave_hull_plugin = plugins.get('concavehull')

        # Verificar si el plugin está disponible
        if not concave_hull_plugin:
            print("Error: El plugin Concave Hull no está disponible o no está activado.")
        else:
            # Asegurarse de que QGIS ha cargado la capa
            app = QApplication.instance()
            app.processEvents()

            # Acceder al plugin Concave Hull
            concave_hull_plugin = plugins.get('concavehull')

            if not concave_hull_plugin:
                print("Error: El plugin Concave Hull no está disponible o no está activado.")
            else:
                try:
                    # Configurar el número de vecinos en QSettings antes de ejecutar el plugin
                    QSettings().setValue('/ConcaveHull/NumberOfNeighbors', 25)


                    # Programar que apenas aparezca un mensaje, lo acepte
                    QTimer.singleShot(100, auto_accept_message_box)

                    # Ejecutar el plugin
                    concave_hull_plugin.execute()
                    
                    print("Concave Hull ejecutado con 25 vecinos.")
                except Exception as e:
                    print(f"Error al ejecutar Concave Hull: {e}")
    # Ruta donde se guardará la capa
    output_path = f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Urban_{mun}.shp'

    # Obtener la capa activa con el nombre 'ConcaveHull'
    layer_to_save = QgsProject.instance().mapLayersByName('ConcaveHull')

    if not layer_to_save:
        print("Error: No se encontró una capa activa denominada 'ConcaveHull'.")
    else:
        # Seleccionar la primera capa con ese nombre (si hubiera más de una)
        layer_to_save = layer_to_save[0]

        # Guardar la capa como shapefile
        options = QgsVectorFileWriter.SaveVectorOptions()
        options.driverName = "ESRI Shapefile"  # Formato del archivo
        options.fileEncoding = "UTF-8"        # Codificación

        result = QgsVectorFileWriter.writeAsVectorFormatV2(
            layer_to_save,
            output_path,
            QgsProject.instance().transformContext(),
            options
        )


    # Define paths
    shapes = f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Urban_{mun}.shp'
    output = f"/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Urban_{mun}_output.shp"
    metrics = "Proximity;Cohesion;Exchange;Spin;Perimeter;Dispers_;Range"
    edge_width = 100

    if edge_width == '#':
        if "Interior" in metrics:
            raise ValueError("\nEDGE WIDTH MUST BE SPECIFIED TO CALCULATE INTERIOR INDEX")
    else:
        edge_width = float(edge_width)


    layer = QgsVectorLayer(shapes, "Input Layer", "ogr")
    if not layer.isValid():
        raise ValueError("No se pudo cargar la capa de entrada.")

    # Copy features to a new output layer
    if not os.path.exists(output):
        QgsVectorFileWriter.writeAsVectorFormat(layer, output, "UTF-8", layer.crs(), "ESRI Shapefile")
        output_layer = QgsVectorLayer(output, "Output Layer", "ogr")

    # Set up temporary workspace
    TempWS = f'/Users/maurocastiella/Desktop/CAF/Planning/Mapas/Shape_Metrics_ArcPro/Sample_shapes/Temp_Maps'
    if not os.path.exists(TempWS):
        os.makedirs(TempWS)

    # Load the output layer
    layer = QgsVectorLayer(output, "output_layer", "ogr")
    if not layer.isValid():
        raise ValueError(f"Layer {output} failed to load.")

    # Add fields for metrics and normalized metrics
    layer.startEditing()
    add_fields(layer)
    layer.updateFields()

    # Iterate over features in the layer to calculate metrics
    for feature in layer.getFeatures():
        metric_dct = {}
        ID = feature.id()

        # Get geometry object for the feature
        ShpGeom = feature.geometry()

        # Calculate shape area and perimeter
        A = ShpGeom.area()
        P = ShpGeom.length()

        # Get shape true centroid
        centroidXY = ShpGeom.centroid().asPoint()

        # Equal area circle parameters
        r = (A / math.pi)**0.5  # Radius of equal area circle
        p = 2 * math.pi * r     # Equal area circle perimeter

        # SECTION 1: Get list of coordinates of perimeter vertices
        gridTxtFile = os.path.join(TempWS, f"Urban_{mun}.txt")
        vertexLst, featPntLst, cellsize, x_offset, y_offset = ConvertToGridPnts(ShpGeom, gridTxtFile) 


        # Adjust centroid coordinates
        Xc, Yc = centroidXY.x() - x_offset, centroidXY.y() - y_offset

        # Update metrics dictionary (e.g., dummy placeholders for actual calculations)
        metric_dct["Proximity"] = 0.0  # Placeholder
        metric_dct["Cohesion"] = 0.0   # Placeholder

        #---------------------------------------------------------------------------
        # SECTION 2: THE COHESION INDEX
        if "Cohesion" in metrics:
            shp_interD = interpointDistance(featPntLst)  # Calculate average interpoint distance
            circ_interD = r * 0.9054  # Avg interpoint distance for an equal area circle
            CohesionIndex = circ_interD / shp_interD  # Cohesion index
            metric_dct["Cohesion"] = [shp_interD, CohesionIndex]
            print(f"\tCohesion calculated: {CohesionIndex}")

        #---------------------------------------------------------------------------
        # SECTION 3: PROXIMITY AND EXCHANGE INDICES
        if "Proximity" in metrics or "Exchange" in metrics:
            D_to_Center, EAC_pix = proximity(featPntLst, [Xc, Yc], r)  # Calculate proximity metrics
            circD = r * (2.0 / 3.0)  # Avg distance to center for equal area circle

            if "Proximity" in metrics:
                ProximityIndex = circD / D_to_Center  # Proximity index
                metric_dct["Proximity"] = [D_to_Center, ProximityIndex]
                print(f"\tProximity calculated: {ProximityIndex}")

            if "Exchange" in metrics:
                inArea = EAC_pix * cellsize**2  # Area within equal area circle
                areaExchange = inArea / A  # Area exchange index
                metric_dct["Exchange"] = [inArea, areaExchange]
                print(f"\tExchange calculated: {areaExchange}")

        #---------------------------------------------------------------------------
        # SECTION 4: SPIN INDEX
        if "Spin" in metrics:
            shpMOI = spin(featPntLst, [Xc, Yc])  # Moment of inertia for the shape
            circ_MOI = 0.5 * r**2  # Moment of inertia for an equal area circle
            Spin = circ_MOI / shpMOI  # Spin index
            metric_dct["Spin"] = [shpMOI, Spin]
            print(f"\tSpin calculated: {Spin}")

        #---------------------------------------------------------------------------
        # SECTION 5: PERIMETER INDEX
        if "Perimeter" in metrics:
            PerimIndex = p / P  # Perimeter index
            metric_dct["Perimeter"] = [P, PerimIndex]
            print(f"\tPerimeter calculated: {PerimIndex}")

        #---------------------------------------------------------------------------
        # SECTION 6: GENERATING PERIMETER POINTS
        if "Depth" in metrics or "Girth" in metrics or "Dispers_" in metrics or "Interior" in metrics:
            perimPntLst = PerimeterPnts(vertexLst, 500)  # Generate points evenly distributed along the perimeter

            #---------------------------------------------------------------------------
            # SECTION 7: DISTANCE OF INTERIOR POINTS TO PERIMETER POINTS
            pt_dToE = pt_distToEdge(featPntLst, perimPntLst)  # Calculate distances

      #------------------------------------------------------------------------------
        # SECTION 8: THE DEPTH INDEX
        if "Depth" in metrics:
            shp_depth = depth(pt_dToE)  # Average distance to nearest edge pixel
            EAC_depth = r / 3  # Depth for an equal area circle
            depthIndex = shp_depth / EAC_depth  # Depth Index
            metric_dct["Depth"] = [shp_depth, depthIndex]
            print(f"\tDepth calculated: {depthIndex}")

        #------------------------------------------------------------------------------
        # SECTION 9: THE GIRTH INDEX
        if "Girth" in metrics:
            shp_Girth = girth(pt_dToE)  # Distance from edge to innermost point
            girthIndex = shp_Girth / r  # Girth Index
            metric_dct["Girth"] = [shp_Girth, girthIndex]
            print(f"\tGirth calculated: {girthIndex}")

        #-------------------------------------------------------------------------------
        # SECTION 14: VIABLE INTERIOR INDEX
        if "Interior" in metrics:
            interiorArea = Interior(pt_dToE, edge_width) * (cellsize**2)  # Area farther than edge width
            circ_interiorArea = math.pi * (r - edge_width)**2  # Interior area for equal area circle
            interiorIndex = interiorArea / circ_interiorArea  # Interior Index
            metric_dct["Interior"] = [interiorArea, interiorIndex]
            print(f"\tInterior calculated: {interiorIndex}")

        #------------------------------------------------------------------------------
        # SECTION 10: DISPERSION INDEX
        if "Dispers_" in metrics:
            dispersionIndex, dispersion = dispersion_fnc([Xc, Yc], perimPntLst[0])  # Avg distance from center
            metric_dct["Dispers_"] = [dispersion, dispersionIndex]
            print(f"\tDispersion calculated: {dispersionIndex}")

        #------------------------------------------------------------------------------
        # SECTION 11: DETOUR INDEX
        if "Detour" in metrics:
            hullPerim = ConvexHull(vertexLst[0])  # Convex hull perimeter
            detourIndex = p / hullPerim  # Detour Index
            metric_dct["Detour"] = [hullPerim, detourIndex]
            print(f"\tDetour calculated: {detourIndex}")

        #------------------------------------------------------------------------------
        # SECTION 12: RANGE INDEX
        if "Range" in metrics:
            circumCircD = Range(vertexLst[0])  # Diameter of circumscribed circle
            rangeIndex = (2 * r) / circumCircD  # Range Index
            metric_dct["Range"] = [circumCircD, rangeIndex]
            print(f"\tRange calculated: {rangeIndex}")

        #------------------------------------------------------------------------------
        # SECTION 13: TRAVERSAL INDEX
        if "Traversal" in metrics:
            perimPntLst = PerimeterPnts(vertexLst, 60)  # Generate points along the perimeter
            fAvgD = traversal_D(perimPntLst)  # Avg traversal distance for shape
            circAvgD = 4 * r / math.pi  # Avg traversal distance for equal area circle
            traversal = circAvgD / fAvgD  # Traversal Index
            metric_dct["Traversal"] = [fAvgD, traversal]
            print(f"\tTraversal calculated: {traversal}")

        # Start timestamp
        start_time = time.time()

        layer.startEditing()

        # Iterate over the layer features
        for feature in layer.getFeatures():
            ID = feature.id()
        

        # Assign values to the corresponding fields
        for metric, values in metric_dct.items():
            value = values[0]  # Valor bruto
            normValue = values[1]  # Valor normalizado
            normName = f"n{metric}"  # Nombre del campo normalizado
            
            # Verificar si los campos existen en la capa
            if metric in layer.fields().names() and normName in layer.fields().names():
                feature.setAttribute(metric, value)
                feature.setAttribute(normName, normValue)

        layer.updateFeature(feature)


    # Save changes
    layer.commitChanges()

    # Compute Area_km2 and Perimeter_km for the final urban polygon layer
    try:
        # Use the final output produced by the metrics pipeline
        urban_output_shp = f"/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Urban_{mun}_output.shp"
        gdf_used = gpd.read_file(urban_output_shp)

        if gdf_used.empty:
            area_km2 = np.nan
            perim_km = np.nan
        else:
            # If it is geographic (degrees), project to a metric CRS first (meters)
            if (gdf_used.crs is not None) and getattr(gdf_used.crs, "is_geographic", False):
                gdf_used = gdf_used.to_crs("EPSG:3438")  # projected (meters)

            geom_used = unary_union(gdf_used.geometry.buffer(0))  # union to avoid double counting shared borders

            # If the layer is projected in meters (e.g., EPSG:3438), compute directly
            if (gdf_used.crs is not None) and (not getattr(gdf_used.crs, "is_geographic", False)) and ("3438" in str(gdf_used.crs)):
                ft_to_m = 0.3048006096012192  # US survey foot to meters
                area_km2 = (geom_used.area * (ft_to_m ** 2)) / 1e6
                perim_km = (geom_used.length * ft_to_m) / 1000
            else:
                # Otherwise assume feet-based units
                ft_to_m = 0.3048006096012192  # US survey foot to meters
                area_km2 = (geom_used.area * (ft_to_m ** 2)) / 1e6
                perim_km = (geom_used.length * ft_to_m) / 1000

    except Exception as e:
        print(f"[Area/Perim] {mun}: error computing area/perimeter: {e}")
        area_km2 = np.nan
        perim_km = np.nan


    # Time
    end_time = time.time()
    print(f"Análisis completado en {(end_time - start_time) / 60:.2f} minutos.")


    # Ruta del shapefile de salida
    output_shp = f"/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Urban_{mun}_output.shp"

    # Asegurar que el ID del municipio está presente
    metric_dct["ID"] = mun  # Donde 'mun' es el código del municipio

    # Expandir las listas dentro de `metric_dct` a valores separados
    expanded_metrics = {}
    for key, value in metric_dct.items():
        if isinstance(value, list):
            expanded_metrics[f"{key}"] = value[0]  # Valor bruto
            expanded_metrics[f"n{key}"] = value[1]  # Valor normalizado
        else:
            expanded_metrics[key] = value  # Agregar directamente si no es una lista

    expanded_metrics["Area_km2"] = area_km2
    expanded_metrics["Perimeter_km"] = perim_km

    # Escribir/añadir la nueva fila al archivo Excel
    if os.path.exists(output_excel):
        # Leer el archivo Excel existente
        existing_df = pd.read_excel(output_excel, engine='openpyxl')
    else:
        # Si no existe, crear un DataFrame vacío con columnas iniciales
        existing_df = pd.DataFrame()

    # Crear un DataFrame con los nuevos datos
    new_row_df = pd.DataFrame([expanded_metrics])

    # Combinar con los datos existentes
    updated_df = pd.concat([existing_df, new_row_df], ignore_index=True)

    # Escribir el DataFrame actualizado al archivo Excel
    updated_df.to_excel(output_excel, index=False, engine='openpyxl')


    # Given that we have now the polygons that represent the Urban Shapes of the Municipality, we can delete the rasters in order to clear some space.
    files_to_delete = [
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Raster_Urban_Area_{mun}.tif',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Raster_{mun}.tif',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Raster_Urban_Area_{mun}.tif.aux.xml',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Raster_{mun}.tif.aux.xml',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Capital_{mun}.shp',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Capital_{mun}.shx',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Capital_{mun}.dbf',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Capital_{mun}.cpg',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Capital_{mun}.prj',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Mun_{mun}.shp',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Mun_{mun}.shx',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Mun_{mun}.dbf',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Mun_{mun}.cpg',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Mun_{mun}.prj',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}.shp',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}.shx',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}.dbf',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}.cpg',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}.prj',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}_temp.shp',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}_temp.shx',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}_temp.dbf',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}_temp.cpg',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}_temp.prj',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}_temp2.shp',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}_temp2.shx',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}_temp2.dbf',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}_temp2.cpg',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}_temp2.prj',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}_temp3.shp',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}_temp3.shx',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}_temp3.dbf',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}_temp3.cpg',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}_temp3.prj',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Generated_points_{mun}.shp',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Generated_points_{mun}.shx',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Generated_points_{mun}.dbf',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Generated_points_{mun}.cpg',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Generated_points_{mun}.prj',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Min_Distances_KM_{mun}.shp',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Min_Distances_KM_{mun}.shx',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Min_Distances_KM_{mun}.dbf',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Min_Distances_KM_{mun}.cpg',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Min_Distances_KM_{mun}.prj',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}_4326.shp',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}_4326.shx',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}_4326.dbf',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}_4326.cpg',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Pol_{mun}_4326.prj',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Capital_{mun}_4326.shp',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Capital_{mun}_4326.shx',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Capital_{mun}_4326.dbf',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Capital_{mun}_4326.cpg',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Capital_{mun}_4326.prj',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Min_Distances_KM_{mun}_4326.shp',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Min_Distances_KM_{mun}_4326.shx',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Min_Distances_KM_{mun}_4326.dbf',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Min_Distances_KM_{mun}_4326.cpg',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Min_Distances_KM_{mun}_4326.prj',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Filtered_Polygons_{mun}.shp',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Filtered_Polygons_{mun}.shx',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Filtered_Polygons_{mun}.dbf',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Filtered_Polygons_{mun}.cpg',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Filtered_Polygons_{mun}.prj',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Filtered_Polygons_{mun}_temp.shp',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Filtered_Polygons_{mun}_temp.shx',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Filtered_Polygons_{mun}_temp.dbf',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Filtered_Polygons_{mun}_temp.cpg',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Filtered_Polygons_{mun}_temp.prj',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Urban_{mun}.shp',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Urban_{mun}.shx',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Urban_{mun}.dbf',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Urban_{mun}.cpg',
        f'/Users/maurocastiella/Desktop/CAF/Planning/Mun_shapefiles/Urban_{mun}.prj',
    ]

    # Borrar los archivos
    for file_path in files_to_delete:
        if os.path.exists(file_path):
            try:
                os.remove(file_path)
            except Exception as e:
                print(f"Error deleting {file_path}: {e}")
        else:
            print(f"File not found: {file_path}")

    # Lista de nombres de capas a eliminar
    layers_to_remove = ["ConcaveHull", f'Filtered Polygons', f'Urban Area Polygons', f'Raster Urban Area']  # Reemplaza con los nombres de tus capas


    # Obtener el proyecto actual
    project = QgsProject.instance()

    # Iterar sobre la lista y eliminar las capas correspondientes
    for layer_name in layers_to_remove:
        layers = project.mapLayersByName(layer_name)
        if layers:
            for layer in layers:
                project.removeMapLayer(layer.id())


