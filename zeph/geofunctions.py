#--------------------------------
# Name:         gdal_common.py
# Purpose:      Common GDAL Support Functions
# Author:       Charles Morton & Andrew Vitale
# Created       2015-07-20
# Python:       2.7
#--------------------------------
from __future__ import absolute_import, division, print_function
import copy
import csv
import datetime as dt
import gc
import itertools
import logging
import math
import os
import random
import re
import warnings

import numpy as np
from osgeo import gdal, ogr, osr

import python_common

################################################################################

class extent:
    """Bounding Geographic Extent"""
    ##def __repr__(self):
    ##    return '<Extent xmin:{0} ymin:{1} xmax:{2} ymax:{3}>'.format(
    ##        self.xmin, self.ymin, self.xmax, self.ymax)
    def __str__(self):
        return '{0} {1} {2} {3}'.format(
            self.xmin, self.ymin, self.xmax, self.ymax)
    def __iter__(self):
        return iter((self.xmin, self.ymin, self.xmax, self.ymax))
    def __init__(self, (xmin, ymin, xmax, ymax), ndigits=10):
        """Round values to avoid Float32 rounding errors"""
        self.xmin = round(xmin, ndigits)
        self.ymin = round(ymin, ndigits)
        self.xmax = round(xmax, ndigits)
        self.ymax = round(ymax, ndigits)
    def adjust_to_snap(self, method='EXPAND', snap_x=None, snap_y=None,
                       cs=None):
        if snap_x is None and env.snap_x is not None:
            snap_x = env.snap_x
        if snap_y is None and env.snap_y is not None:
            snap_y = env.snap_y
        if cs is None:
            if env.cellsize:
                cs = env.cellsize
            else:
                raise SystemExit('Cellsize was not set')
        if method.upper() == 'ROUND':
            self.xmin = math.floor((self.xmin - snap_x) / cs + 0.5) * cs + snap_x
            self.ymin = math.floor((self.ymin - snap_y) / cs + 0.5) * cs + snap_y
            self.xmax = math.floor((self.xmax - snap_x) / cs + 0.5) * cs + snap_x
            self.ymax = math.floor((self.ymax - snap_y) / cs + 0.5) * cs + snap_y
        elif method.upper() == 'EXPAND':
            self.xmin = math.floor((self.xmin - snap_x) / cs) * cs + snap_x
            self.ymin = math.floor((self.ymin - snap_y) / cs) * cs + snap_y
            self.xmax = math.ceil((self.xmax - snap_x) / cs) * cs + snap_x
            self.ymax = math.ceil((self.ymax - snap_y) / cs) * cs + snap_y
        elif method.upper() == 'SHRINK':
            self.xmin = math.ceil((self.xmin - snap_x) / cs) * cs + snap_x
            self.ymin = math.ceil((self.ymin - snap_y) / cs) * cs + snap_y
            self.xmax = math.floor((self.xmax - snap_x) / cs) * cs + snap_x
            self.ymax = math.floor((self.ymax - snap_y) / cs) * cs + snap_y
    def buffer_extent(self, distance):
        self.xmin -= distance
        self.ymin -= distance
        self.xmax += distance
        self.ymax += distance
    def split_extent(self):
        """List of extent terms (xmin, ymin, xmax, ymax)"""
        return self.xmin, self.ymin, self.xmax, self.ymax
    def copy(self):
        """Return a copy of the extent"""
        return extent((self.xmin, self.ymin, self.xmax, self.ymax))
    def corner_points(self):
        """Corner points in clockwise order starting with upper-left point"""
        return [(self.xmin, self.ymax), (self.xmax, self.ymax),
                (self.xmax, self.ymin), (self.xmin, self.ymin)]
    def ul_lr_swap(self):
        """Copy of extent object reordered as xmin, ymax, xmax, ymin

        Some gdal utilities want the extent described using upper-left and
        lower-right points.
            gdal_translate -projwin ulx uly lrx lry
            gdal_merge -ul_lr ulx uly lrx lry

        """
        return extent((self.xmin, self.ymax, self.xmax, self.ymin))
    def ogrenv_swap(self):
        """Copy of extent object reordered as xmin, xmax, ymin, ymax

        OGR feature (shapefile) extents are different than GDAL raster extents
        """
        return extent((self.xmin, self.xmax, self.ymin, self.ymax))
    def origin(self):
        """Origin (upper-left corner) of the extent"""
        return (self.xmin, self.ymax)
    def center(self):
        """Centroid of the extent"""
        return ((self.xmin + 0.5 * (self.xmax - self.xmin)),
                (self.ymin + 0.5 * (self.ymax - self.ymin)))
    def shape(self, cs=None):
        """Return number of rows and columns of the extent
        Args:
            cs: cellsize (default to env.cellsize if not set)
        Returns:
            tuple of raster rows and columns
        """
        if cs is None and env.cellsize:
            cs = env.cellsize
        cols = int(round(abs((self.xmin - self.xmax) / cs), 0))
        rows = int(round(abs((self.ymax - self.ymin) / -cs), 0))
        return rows, cols
    def geo(self, cs=None):
        """Geo-tranform of the extent"""
        if cs is None:
            if env.cellsize:
                cs = env.cellsize
            else:
                raise SystemExit('Cellsize was not set')
        return (self.xmin, abs(cs), 0., self.ymax, 0., -abs(cs))
    def geometry(self):
        """GDAL geometry object of the extent"""
        ring = ogr.Geometry(ogr.wkbLinearRing)
        for point in self.corner_points():
            ring.AddPoint(point[0], point[1])
        ring.CloseRings()
        polygon = ogr.Geometry(ogr.wkbPolygon)
        polygon.AddGeometry(ring)
        return polygon
    ##def square(self, method='EXPAND', cs=None):
    ##    """Compute a square extent
    ##
    ##    This could probably be done in one step by looking at the sign
    ##    of the difference
    ##    """
    ##    if cs is None and env.cellsize:
    ##        cs = env.cellsize
    ##    width = self.xmax - self.xmin
    ##    height = self.ymax - self.ymin
    ##    diff = abs(width - height)
    ##    if width == height:
    ##        pass
    ##    elif method.upper() == 'EXPAND':
    ##        if width > height:
    ##            self.xmin = self.xmin
    ##            self.ymin = self.ymin - (0.5 * diff)
    ##            self.xmax = self.xmax
    ##            self.ymax = self.ymax + (0.5 * diff)
    ##        elif width < height:
    ##            self.xmin = self.xmin - (0.5 * diff)
    ##            self.ymin = self.ymin
    ##            self.xmax = self.xmax + (0.5 * diff)
    ##            self.ymax = self.ymax
    ##    elif method.upper() == 'SHRINK':
    ##        if width > height:
    ##            self.xmin = self.xmin + (0.5 * diff)
    ##            self.ymin = self.ymin
    ##            self.xmax = self.xmax - (0.5 * diff)
    ##            self.ymax = self.ymax
    ##        elif width < height:
    ##            self.xmin = self.xmin
    ##            self.ymin = self.ymin + (0.5 * diff)
    ##            self.xmax = self.xmax
    ##            self.ymax = self.ymax - (0.5 * diff)
    ##    elif method.upper() == 'ROUND':
    ##        ## Expand and shrink half of difference
    ##        if width > height:
    ##            self.xmin = self.xmin + (0.25 * diff)
    ##            self.ymin = self.ymin - (0.25 * diff)
    ##            self.xmax = self.xmax - (0.25 * diff)
    ##            self.ymax = self.ymax + (0.25 * diff)
    ##        elif width < height:
    ##            self.xmin = self.xmin - (0.25 * diff)
    ##            self.ymin = self.ymin + (0.25 * diff)
    ##            self.xmax = self.xmax + (0.25 * diff)
    ##            self.ymax = self.ymax - (0.25 * diff)
   
class env:
    """"Generic enviornment parameters used in gdal_common"""
    snap_proj, snap_osr, snap_geo = None, None, None
    snap_gcs_proj, snap_gcs_osr = None, None
    ##snap_extent = extent((0,0,1,1))
    cellsize, snap_x, snap_y = None, None, None
    mask_geo, mask_path, mask_array = None, None, None
    mask_extent = extent((0,0,1,1))
    mask_gcs_extent = extent((0,0,1,1))
    mask_rows, mask_cols = 0, 0
    
##    def set_snap_raster(self, snap_raster):
##        if not os.path.isfile(snap_raster):
##            logging.error(
##                '\nERROR: The snap_raster path {0} is not valid'.format(
##                    snap_raster))
##            raise SystemExit()
##        snap_ds = gdal.Open(snap_raster, 0)
##        self.snap_geo = raster_ds_geo(snap_ds)
##        self.snap_extent = raster_ds_extent(snap_ds)
##        self.snap_proj = snap_ds.GetProjection()
##        self.snap_osr = osr.SpatialReference()
##        self.snap_osr.ImportFromWkt(self.snap_proj)
##        self.snap_gcs_osr = self.snap_osr.CloneGeogCS()
##        self.snap_gcs_proj = self.snap_gcs_osr.ExportToWkt()
##        self.cellsize = geo_cellsize(self.snap_geo, x_only=True)
##        self.snap_x, self.snap_y = geo_origin(self.snap_geo)
##        snap_ds = None
##        del snap_ds

def raster_path_ds(raster_path, read_only=True):
    """Get the :class:`gdal.Dataset` of the raster.

    Args:
        raster_path (str): file path to raster
        read_only (bool): if True, raster is opened with the
            gdal read only code

    Return:
        :class:`gdal.Dataset`: 

    """
    if read_only:
        return gdal.Open(raster_path, 0)
    else:
        return gdal.Open(raster_path, 1)
def raster_path_env(raster_path, mask_array=True):
    """:class:`gdal_common.env` from a raster path.

    Args:
        raster_path (str): file path to raster
        mask_array (bool): if True, a mask_array is read into
            the :class:`gdal_common` environment

    Return:
        :class:`gdal_common.env`

    """
    input_ds = gdal.Open(raster_path, 0)
    return raster_ds_env(input_ds, mask_array)
def raster_ds_env(raster_ds, mask_array=True):
    """Create :class:`gdal_common.env` from a :class:`gdal.Dataset`.    

    Args:
        raster_ds (:class:`gdal.Dataset`): an opened :class:`gdal.Dataset`
        mask_array (bool): if True, a mask_array is read into
            the :class:`gdal_common` environment

    Return:
        :class:`gdal_common.env`

    """
    environment = env()
    environment.mask_geo = raster_ds_geo(raster_ds)
    environment.mask_rows, environment.mask_cols = raster_ds_shape(raster_ds)
    environment.mask_extent = geo_extent(
        environment.mask_geo, environment.mask_rows, environment.mask_cols)
    environment.mask_proj = raster_ds_proj(raster_ds)
    if mask_array:
        environment.mask_array
    environment.snap_geo = raster_ds_geo(raster_ds)
    environment.snap_osr = raster_ds_osr(raster_ds)
    environment.snap_proj = raster_ds_proj(raster_ds)
    environment.snap_x, environment.snap_y = 0, 0
    return environment



def raster_driver(raster_path):
    """Get the GDAL driver from a raster path

    Currently supports ERDAS Imagine format, GeoTiff,
    HDF-EOS (HDF4), BSQ/BIL/BIP, and memory drivers.

    Args:
        raster_path (str): filepath to a raster

        
    Returns:
        GDAL driver: GDAL raster driver

    """
    if raster_path.upper().endswith('IMG'):
        return gdal.GetDriverByName('HFA')
    elif raster_path.upper().endswith('TIF'):
        return gdal.GetDriverByName('GTiff')
    elif raster_path.upper().endswith('HDF'):
        return gdal.GetDriverByName('HDF4')
    elif raster_path[-3:].upper() in ['BSQ', 'BIL', 'BIP']:
        return gdal.GetDriverByName('EHdr')
    elif raster_path == '':
        return gdal.GetDriverByName('MEM')
    else:
        raise SystemExit()

def numpy_to_gdal_type(numpy_type):
    """Set the GDAL raster data type based on the numpy array data type

    The following built in functions do roughly the same thing
    NumericTypeCodeToGDALTypeCode
    GDALTypeCodeToNumericTypeCode

    Args:
        numpy_type (:class:`np.dtype`): numpy array type (i.e. np.bool, np.float32, etc)
    
    Returns:
        g_type: GDAL `datatype <http://www.gdal.org/gdal_8h.html#a22e22ce0a55036a96f652765793fb7a4/>`
        _equivalent to the input NumPy :class:`np.dtype`
        g_nodata: Nodata value for GDAL which defaults to the 
        minimum value for the number type

    """
    if numpy_type == np.bool:
        g_type = gdal.GDT_Byte
        g_nodata = 0
    elif numpy_type == np.int:
        g_type = gdal.GDT_Int32
        g_nodata = int(np.iinfo(np.int32).min)
    elif numpy_type == np.int8:
        g_type = gdal.GDT_Int16
        g_nodata = int(np.iinfo(np.int8).min)
    elif numpy_type == np.int16:
        g_type = gdal.GDT_Int16
        g_nodata = int(np.iinfo(np.int16).min)
    elif numpy_type == np.int32:
        g_type = gdal.GDT_Int32
        g_nodata = int(np.iinfo(np.int32).min)
    elif numpy_type == np.uint8:
        g_type = gdal.GDT_Byte
        g_nodata = int(np.iinfo(np.uint8).max)
    elif numpy_type == np.uint16:
        g_type = gdal.GDT_UInt16
        g_nodata = int(np.iinfo(np.uint16).max)
    elif numpy_type == np.uint32:
        g_type = gdal.GDT_UInt32
        g_nodata = int(np.iinfo(np.uint32).max)
    elif numpy_type == np.float:
        g_type = gdal.GDT_Float32
        g_nodata = float(np.finfo(np.float32).min)
    ##elif numpy_type == np.float16:
    ##    g_type = gdal.GDT_Float32
    ##    g_nodata = float(np.finfo(np.float16).min)
    elif numpy_type == np.float32:
        g_type = gdal.GDT_Float32
        g_nodata = float(np.finfo(np.float32).min)
    elif numpy_type == np.float64:
        g_type = gdal.GDT_Float32
        g_nodata = float(np.finfo(np.float32).min)
    ##elif numpy_type == np.int64:   g_type = gdal.GDT_Int32
    ##elif numpy_type == np.uint64:  g_type = gdal.GDT_UInt32
    ##elif numpy_type == np.complex:    g_type = gdal.GDT_CFloat32
    ##elif numpy_type == np.complex64:  g_type = gdal.GDT_CFloat32
    ##elif numpy_type == np.complex128: g_type = gdal.GDT_CFloat32
    ##else: numpy_type, m_type_max = gdal.GDT_Unknown
    else:
        g_type, g_nodata = None, None
    return g_type, g_nodata

def gdal_to_numpy_type(gdal_type):
    """Return the NumPy array data type based on a GDAL type

    Args:
        gdal_type (:class:`gdal.type`): GDAL data type

    Returns:
        numpy_type: NumPy datatype (:class:`np.dtype`)

    """
    #### Set the NumPy array type based on the GDAL raster type
    if gdal_type == gdal.GDT_Unknown:
        numpy_type = np.float64
    elif gdal_type == gdal.GDT_Byte:
        numpy_type = np.uint8
    elif gdal_type == gdal.GDT_UInt16:
        numpy_type = np.uint16
    elif gdal_type == gdal.GDT_Int16:
        numpy_type = np.int16
    elif gdal_type == gdal.GDT_UInt32:
        numpy_type = np.uint32
    elif gdal_type == gdal.GDT_Int32:
        numpy_type = np.int32
    elif gdal_type == gdal.GDT_Float32:
        numpy_type = np.float32
    elif gdal_type == gdal.GDT_Float64:
        numpy_type = np.float64
    ##elif gdal_type == gdal.GDT_CInt16:
    ##    numpy_type = np.complex64
    ##elif gdal_type == gdal.GDT_CInt32:
    ##    numpy_type = np.complex64
    ##elif gdal_type == gdal.GDT_CFloat32:
    ##    numpy_type = np.complex64
    ##elif gdal_type == gdal.GDT_CFloat64:
    ##    numpy_type = np.complex64
    return numpy_type

def polygon_to_raster_ds(feature_path, nodata_value=0, burn_value=1, 
                         output_osr=None, output_cs=None, output_extent=None):
    """Convert a raster dataset based on a feature file path

    Args:
        feature_path (str): Filepath to the vector data
        nodata_value (int, float): No data value of the output raster
        burn_value (int, float): Value to be assigned to the raster where 
            the polygon is present
        output_osr (osr.SpatialReference): Desired spatial reference of 
            the output as an OSR object. If None, checks for a :class:`gdc.env` value
        output_cs (int): Desired cell size of the output raster. If None,
            checks for a :class:`gdc.env` value
        output_extent: Desired extent of the output raster dataset. If None,
            checks for a :class:`gdc.env` value

    Returns:
        GDAL raster dataset :class:`gdal.ds` with burn value where polygon is present
    """
    feature_ds = ogr.Open(feature_path)
    feature_lyr = feature_ds.GetLayer()
    ## Check that projection matches snap_raster                           
    if output_osr is None and env.snap_osr:
        output_osr = env.snap_osr
    if output_cs is None and env.cellsize:
        output_cs = env.cellsize
    if output_extent is None:
        raster_extent = feature_lyr_extent(feature_lyr)
        raster_extent.adjust_to_snap('EXPAND', cs=output_cs)
    else:
        raster_extent = output_extent
    ## DEADBEEF - Commented out because interpolator is having problems with the
    ##   USGS central valley shapefile converting to PROJ4
    ##feature_osr = feature_lyr.GetSpatialRef()
    ##if not matching_spatref(feature_osr, output_osr):
    ##    print (('\nERROR: The mask feature projection does '+
    ##            'not match the snap raster projection'))
    ##    raise SystemExit()
    raster_rows, raster_cols = raster_extent.shape(output_cs)
    mem_driver = gdal.GetDriverByName('MEM') 
    raster_ds = mem_driver.Create(
        '', raster_cols, raster_rows, 1, gdal.GDT_Byte)
    raster_ds.SetProjection(output_osr.ExportToWkt())
    raster_ds.SetGeoTransform(raster_extent.geo(output_cs))
    raster_band = raster_ds.GetRasterBand(1)
    raster_band.Fill(nodata_value)
    raster_band.SetNoDataValue(nodata_value)
    gdal.RasterizeLayer(
        raster_ds, [1], feature_lyr, burn_values=[burn_value])
    feature_ds = None
    return raster_ds

def raster_to_polygon(raster_path, polygon_path, layer_name='OUTPUT_POLY'):
    """Create a polygon file from a raster filepath

    Args:
        raster_path (str): Filepath to the input raster that's to be converted
        polygon_path (str): Filepath of the desired output polygon
        layer_name (str): Layer name assigned to the polygon
        
    Returns:
        None. Operates on disk.

    """
    raster_ds = gdal.Open(raster_path)
    raster_ds_to_polygon(raster_ds, polygon_path, layer_name)
    raster_ds = None
def raster_ds_to_polygon(raster_ds, polygon_path, layer_name='OUTPUT_POLY'):
    """Create a polygon file from a GDAL raster dataset

    Args:
        raster_ds (:class:`gdal.Dataset`): The GDAL raster dataset that is 
            to be converted to a polygon
        polygon_path (str): The filepath of the output polygon file
        layer_name (str): The layer name assigned to the polygon

    Returns:
        None. Operates on disk.

    """
    shp_driver = ogr.GetDriverByName('ESRI Shapefile')
    if os.path.isfile(polygon_path):
        shp_driver.DeleteDataSource(polygon_path)
    polygon_ds = shp_driver.CreateDataSource(polygon_path)
    polygon_lyr = polygon_ds.CreateLayer(layer_name, geom_type=ogr.wkbPolygon)
    field_defn = ogr.FieldDefn('VALUE', ogr.OFTInteger)    
    polygon_lyr.CreateField(field_defn)
    ## Convert raster to polygon
    raster_band = raster_ds.GetRasterBand(1)
    gdal.Polygonize(raster_band, raster_band, polygon_lyr, 0)
    polygon_ds = None
    ## Format spatial reference for prj file
    polygon_osr = proj_osr(env.snap_proj)
    polygon_osr.MorphToESRI()
    polygon_proj = polygon_osr.ExportToWkt()    
    ## Write projection/spatial reference
    prj_file = open(polygon_path.replace('.shp','.prj'), 'w')
    prj_file.write(polygon_proj)
    prj_file.close()

def polygon_buffer(input_path, output_path, buffer_distance):
    """Buffers a polygon feature by the specified amount and writes
    the output polygon to disk

    Args: 
        input_path (str): Filepath of the input polygons that are to be buffered
        output_path (str): Filepath of the output polyons with the buffer applied
        buffer_distance (int, float): Desired distance of buffering in the 
            unit of the projection

    Returns:
        None. Operates on disk.

    """
    shp_driver = ogr.GetDriverByName('ESRI Shapefile')
    input_ds = shp_driver.Open(input_path, 0)
    output_ds = shp_driver.CopyDataSource(input_ds, output_path)
    output_ds, input_ds = None, None
    del input_ds, output_ds
    output_ds = shp_driver.Open(output_path, 1)
    output_layer = output_ds.GetLayer()
    output_ftr = output_layer.GetNextFeature() 
    while output_ftr:
        output_fid = output_ftr.GetFID()
        ##logging.info('    {0}'.format(output_fid))
        output_geom = output_ftr.GetGeometryRef()
        buffer_geom = output_geom.Clone().Buffer(buffer_distance)
        ## DEADBEEF - Need logic for handling small polygons
        ##if buffer_geom.IsEmpty() and min_zone_pixel_count == 0:
        ##    logging.info('\n    {0}'.format(buffer_geom))
        ##    logging.info('    {0}'.format(zone_geom))
        ##    zone_centroid = ogr.Geometry(ogr.wkbPoint)
        ##    zone_centroid = zone_geom.Centroid()
        ##    logging.info('    {0}'.format(zone_centroid))
        ##    ##zone_ftr.SetGeometry(buffer_geom)
        ##    ##zone_layer.SetFeature(zone_ftr)
        ##    raw_input('Press ENTER')
        #### DEADBEEF - Uncomment to remove small buffered polygons
        ##if buffer_geom.IsEmpty() and min_zone_pixel_count > 0:
        if buffer_geom.IsEmpty():
            output_layer.DeleteFeature(output_fid)
        else:
            output_ftr.SetGeometry(buffer_geom)
            output_layer.SetFeature(output_ftr)
        ##output_layer.SetFeature(zone_ftr)
        output_geom, buffer_geom = None, None
        del output_geom, buffer_geom
        output_ftr = output_layer.GetNextFeature()
    ## DEADBEEF - Uncomment to remove small buffered polygons
    output_ds.ExecuteSQL(
        "REPACK {0}".format(output_layer.GetName())) 
    output_ftr = None
    output_ds = None
    del output_ds, output_layer, output_ftr

def matching_spatref(osr_a, osr_b):
    """Test if two spatial reference objects match

    Args:
        osr_a: OSR spatial reference object
        osr_b: OSR spatial reference object

    Returns:
        Bool: True if OSR objects match. Otherwise, False.

    """
    osr_a.MorphToESRI()
    osr_b.MorphToESRI()
    if ((osr_a.GetAttrValue('GEOGCS') == osr_b.GetAttrValue('GEOGCS')) and
        (osr_a.GetAttrValue('PROJECTION') == osr_b.GetAttrValue('PROJECTION')) and
        (osr_a.GetAttrValue('UNIT') == osr_b.GetAttrValue('UNIT')) and
        (osr_a.GetUTMZone() == osr_b.GetUTMZone())):
        return True
    else:
        return False

def osr_proj(input_osr):
    """Return the projection WKT of a spatial reference object

    Args:
        input_osr (:class:`osr.SpatialReference`): the input OSR 
            spatial reference

    Returns:
        WKT: :class:`osr.SpatialReference` in WKT format

    """
    return input_osr.ExportToWkt()
def proj_osr(input_proj):
    """Return the spatial reference object of a projection WKT

    Args:
        input_proj (:class:`osr.SpatialReference` WKT): Input 
            WKT formatted :class:`osr.SpatialReference` object
            to be used in creation of an :class:`osr.SpatialReference`

    Returns:
        osr.SpatialReference: OSR SpatialReference object as represented
            by the input WKT

    """
    input_osr = osr.SpatialReference()
    input_osr.ImportFromWkt(input_proj)
    return input_osr
def epsg_osr(input_epsg):
    """Return the spatial reference object of an EPSG code

    Args:
        input_epsg (int): EPSG spatial reference code as integer

    Returns:
        osr.SpatialReference: :class:`osr.SpatialReference` object

    """
    input_osr = osr.SpatialReference()
    input_osr.ImportFromEPSG(input_epsg)
    return input_osr
def epsg_proj(input_epsg):
    """Return the projecttion WKT of an EPSG code

    Args:
        input_epsg (int): EPS spatial reference code as an integer

    Returns:
        WKT: Well known text rerpresentation of :class:`osr.SpatialReference`
            object

    """
    return osr_proj(epsg_osr(input_epsg))
def proj4_osr(input_proj4):
    """Return the spatial reference object of a PROJ4 code

    Args:
        input_proj4 (str): Proj4 string representing a projection or GCS

    Returns:
        osr.SpatialReference: :class:`osr.SpatialReference` of the input proj4

    """
    input_osr = osr.SpatialReference()
    input_osr.ImportFromProj4(input_proj4)
    return input_osr
def osr_proj4(input_osr):
    """Return the PROJ4 code of an osr.SpatialReference

    Args:
        input_osr (:class:`osr.SpatialReference`): OSR Spatial reference
            of the input projection/GCS

    Returns:
        str: Proj4 string of the projection or GCS

    """
    return input_osr.ExportToProj4()

def raster_path_osr(raster_path):
    """Return the spatial reference of a raster

    Args:
        raster_path (str): The filepath of the input raster

    Returns:
        osr.SpatialReference: :class:`osr.SpatialReference` object
            that defines the input raster's project/GCS

    """
    raster_ds = gdal.Open(raster_path, 0)
    raster_osr = raster_ds_osr(raster_ds)
    raster_ds = None
    return raster_osr
def raster_ds_osr(raster_ds):
    """Return the spatial reference of an opened raster dataset

    Args:
        raster_ds (:class:`gdal.Dataset`): An input GDAL raster dataset

    Returns:
        osr.SpatialReference: :class:`osr.SpatialReference` of a raster
            dataset

    """
    return proj_osr(raster_ds_proj(raster_ds))
def raster_proj_osr(raster_proj):
    """Return the spatial reference of a projection WKT

    Args:
        raster_proj ():
        
    Returns:
        
    """
    warnings.warn(
        ('Function raster_proj_osr() is deprecated. ' +
         'Use gdal_common.proj_osr() instead.'))
    raster_osr = osr.SpatialReference()
    raster_osr.ImportFromWkt(raster_proj)
    return raster_osr  

def feature_path_osr(feature_path):
    """Return the spatial reference of a feature path

    Args:
        feature_path (str): file path to the OGR supported feature

    Returns:
        osr.SpatialReference: :class:`osr.SpatialReference` of the 
            input feature file path

    """
    feature_ds = ogr.Open(feature_path)
    feature_osr = feature_ds_osr(feature_ds)
    feature_ds = None
    return feature_osr
def feature_ds_osr(feature_ds):
    """Return the spatial reference of an opened feature dataset

    Args:
        feature_ds (:class:`ogr.Datset`): Opened feature dataset
            from which you desire the spatial reference

    Returns:
        osr.SpatialReference: :class:`osr.SpatialReference` of the input
            OGR feature dataset

    """
    feature_lyr = feature_ds.GetLayer()
    return feature_lyr_osr(feature_lyr)
def feature_lyr_osr(feature_lyr):
    """Return the spatial reference of a feature layer

    Args:
        feature_lyr (:class:`ogr.Layer`): OGR feature layer from
            which you desire the :class:`osr.SpatialReference`

    Returns:
        osr.SpatialReference: the :class:`osr.SpatialReference` object
            of the input feature layer

    """
    return feature_lyr.GetSpatialRef()

def raster_path_proj(raster_path):
    """Return the projection WKT of a raster

    Args:
        raster_path (str): filepath of the input raster

    Returns:
        str: Well Known Text (WKT) string of the input raster path's
            geographic projection or coordinate system

    """
    raster_ds = gdal.Open(raster_path, 0)
    raster_proj = raster_ds_proj(raster_ds)
    raster_ds = None
    return raster_proj
def raster_ds_proj(raster_ds):
    """Return the projection WKT of an opened raster dataset

    Args:
        raster_ds (:class:`gdal.Dataset`): An opened GDAL raster
            dataset

    Returns:
        str: Well known text (WKT) formatted represetnation of the projection

    """
    return raster_ds.GetProjection()
def raster_osr_proj(raster_osr):
    """DEADBEEF - Deprecated, use osr_proj() instead"""
    warnings.warn(
        ('Function raster_osr_proj() is deprecated. ' +
         'Use gdal_common.osr_proj() instead.'))
    return raster_osr.ExportToWkt()

def path_extent(file_path):
    """Get the extent from a generic file path

    Supports shapefiles, ERDAS Imagine formatted rasters,
    and GeoTiffs

    Args:
        file_path (str): String of the input file path

    Returns:
        gdal_common.extent: :class:`gdal_common.extent` of the 
            input raster or feature set

    """
    if os.path.splitext(file_path)[-1].lower() in ['.shp']:
        return feature_path_extent(file_path)
    elif os.path.splitext(file_path)[-1].lower() in ['.img', '.tif']:
        return raster_path_extent(file_path)
    else:
        logging.error('\nERROR: extent_path was an unrecognized format\n')
        raise SystemExit()

def feature_path_extent(feature_path):
    """"Return the bounding extent of a feature path

    Args:
        feature_path (str): file path to the feature

    Returns:
        gdal_common.extent: :class:`gdal_common.extent` of the
            input feature path

    """
    feature_ds = ogr.Open(feature_path, 0)
    feature_extent = feature_ds_extent(feature_ds)
    feature_ds = None
    return feature_extent    
def feature_ds_extent(feature_ds):
    """"Return the bounding extent of an opened feature dataset

    Args:
        feature_ds (:class:`ogr.Dataset`): An opened feature dataset
            from OGR

    Returns:
        gdal_common.extent: :class:`gdal_common.extent` of the input
            feature dataset

    """
    feature_lyr = feature_ds.GetLayer()
    feature_extent = feature_lyr_extent(feature_lyr)
    return feature_extent
def feature_lyr_extent(feature_lyr):
    """Return the extent of an opened feature layer

    Args:
        feature_lyr (:class:`ogr.Layer`): An OGR feature
            layer

    Returns:
        gdal_common.extent: :class:`gdal_common.extent` of the 
            input feature layer

    """
    ## OGR Extent format (xmin, xmax, ymin, ymax)
    ## ArcGIS/GDAL(?) Extent format (xmin, ymin, xmax, ymax)
    f_extent = extent(feature_lyr.GetExtent())
    f_env = f_extent.ogrenv_swap()
    ##f_extent.ymin, f_extent.xmax = f_extent.xmax, f_extent.ymin
    return f_env

def raster_path_geo(raster_path):
    """Return the geo-transform of a raster

    Args:
        raster_path (str): File path of the input raster

    Returns:
        tuple: :class:`gdal.Geotransform` of the raster the
            input file path points to

    """
    raster_ds = gdal.Open(raster_path, 0)
    raster_geo = raster_ds_geo(raster_ds)
    raster_ds = None
    return raster_geo
def raster_ds_geo(raster_ds):
    """Return the geo-transform of an opened raster dataset

    Args:
        raster_ds (:class:`gdal.Dataset`): An Opened gdal raster dataset

    Returns:
        tuple: :class:`gdal.Geotransform` of the input dataset

    """
    return round_geo(raster_ds.GetGeoTransform())
def round_geo(geo, n=10):
    """Round the values of a geotransform to n digits

    Args:
        geo (tuple): :class:`gdal.Geotransform` object
        n (int): number of digits to round the 
            :class:`gdal.Geotransform` to

    Returns:
        tuple: :class:`gdal.Geotransform` rounded to n digits

    """
    return tuple([round(i,n) for i in geo])

def raster_path_extent(raster_path):
    """Return the extent of a raster

    Args:
        raster_path (str): File path of the input raster

    Returns:
        tuple: :class:`gdal_common.extent` of the raster file path

    """
    raster_ds = gdal.Open(raster_path, 0)
    raster_extent = raster_ds_extent(raster_ds)
    raster_ds = None
    return raster_extent
def raster_ds_extent(raster_ds):
    """Return the extent of an opened raster dataset

    Args:
        raster_ds (:class:`gdal.Dataset`): An opened GDAL raster
            dataset

    Returns:
        tuple: :class:`gdal_common.extent` of the input dataset

    """
    raster_rows, raster_cols = raster_ds_shape(raster_ds)
    raster_geo = raster_ds_geo(raster_ds)
    return geo_extent(raster_geo, raster_rows, raster_cols)
def raster_path_subdataset_extent(raster_path, sd=0):
    """Return the extent of a raster subdataset

    Args:
        raster_path (str): filepath to the raster
        sd (int): subdataset given as an integer, 0 indexed

    Returns:
        tuple: :class:`gdal_common.extent`

    """
    input_ds = gdal.Open(raster_path, 0)
    subdataset = input_ds.GetSubDatasets()[sd][0]
    raster_ds = gdal.Open(subdataset, 0)
    raster_rows, raster_cols = raster_ds_shape(raster_ds)
    raster_geo = raster_ds_geo(raster_ds)
    input_ds, raster_ds = None, None
    return geo_extent(raster_geo, raster_rows, raster_cols)

def raster_path_cellsize(raster_path, x_only=False):
    """Return pixel width & pixel height of raster


    Args:
        raster_path (str): filepath to the raster
        x_only (bool): If True, only return cell width
        
    Returns:
        float: cellsize of the input raster filepath
    """
    raster_ds = gdal.Open(raster_path, 0)
    raster_cellsize = raster_ds_cellsize(raster_ds, x_only)
    raster_ds = None
    return raster_cellsize
def raster_ds_cellsize(raster_ds, x_only=False):
    """Return pixel width & pixel height of an opened raster dataset

    Args:
        raster_ds (:class:`gdal.Dataset`): the input GDAL raster dataset
        x_only (bool): If True, only return cell width

    Returns:
        float: Cellsize of input raster dataset

    """
    return geo_cellsize(raster_ds_geo(raster_ds), x_only)
def geo_cellsize(raster_geo, x_only=False):
    """Return pixel width & pixel height of geo-transform

    Args:
        raster_geo (tuple): :class:`gdal.Geotransform` object
        x_only (bool): If True, only return cell width
        
    Returns:
        tuple: tuple containing the x or x and y cellsize
    """
    if x_only:
        return raster_geo[1]
    else:
        return (raster_geo[1], raster_geo[5])

def raster_path_origin(raster_path):
    """Return upper-left corner of raster

    Returns the upper-left corner coordinates of a raster file path,
    with the coordinates returned in the same projection/GCS as the
    input raster file.

    Args:
        raster_path (str): The raster filepath

    Returns:
        tuple:
        raster_origin: (x, y) coordinates of the upper left corner

    """
    raster_ds = gdal.Open(raster_path, 0)
    raster_origin = raster_ds_origin(raster_ds)
    raster_ds = None
    return raster_origin
def raster_ds_origin(raster_ds):
    """Return upper-left corner of an opened raster dataset

    Returns the upper-left corner coorindates of an open GDAL raster
    dataset with the coordinates returned in the same project/GCS as the
    input raster dataset.

    Args:
        raster_ds (:class:`GDAL.Dataset`): Open GDAL raster dataset

    Returns:
        tuple:
        raster_origin: (x, y) coordinates of the upper left corner

    """
    return geo_origin(raster_ds_geo(raster_ds))
def geo_origin(raster_geo):
    """Return upper-left corner of geo-transform

    Returns the upper-left corner cordinates of :class:`GDAL.Geotransform`
    with the coordinates returned in the same projection/GCS as the input
    geotransform.

    Args:
        raster_geo (:class:`GDAL.Geotransform`): Input GDAL Geotransform

    Returns:
        tuple:
        raster_origin: (x, y) coordinates of the upper left corner

    """
    return (raster_geo[0], raster_geo[3])
def extent_origin(raster_extent):
    """Return upper-left corner of an extent

    Deprecated, use extent.origin() method

    Args:
        raster_extent:

    Returns:
        tuple
    """
    warnings.warn(
        ('Function extent_origin() is deprecated. ' +
         'Use gdal_common.extent.origin() method instead.'))
    return (raster_extent.xmin, raster_extent.ymax)

def geo_extent(geo, rows, cols):
    """Return the extent from a geo-transform and array shape

    This function takes the :class:`GDAL.Geotransform`, number of 
    rows, and number of columns in a 2-dimensional :class:`np.array` 
    (the :class:`np.array.shape`),and returns a :class:`gdc.extent`
    
    Geo-transform can be UL with +/- cellsizes or LL with +/+ cellsizes
    This approach should also handle UR and RR geo-transforms
    
    Returns ArcGIS/GDAL Extent format (xmin, ymin, xmax, ymax) but
        OGR Extent format (xmin, xmax, ymax, ymin) can be obtained using the
        extent.ul_lr_swap() method

    Args:
        geo (tuple): :class:`gdal.Geotransform` object
        rows (int): number of rows
        cols (int): number of cols

    Returns:
        gdal_common.extent:
        A :class:`gdal_common.extent` class object
        
    """
    cs_x, cs_y = geo_cellsize(geo, x_only=False)
    origin_x, origin_y = geo_origin(geo)
    ## ArcGIS/GDAL Extent format (xmin, ymin, xmax, ymax)
    return extent([min([origin_x + cols * cs_x, origin_x]),
                   min([origin_y + rows * cs_y, origin_y]),
                   max([origin_x + cols * cs_x, origin_x]),
                   max([origin_y + rows * cs_y, origin_y])])
    ## OGR Extent format (xmin, xmax, ymax, ymin)
    ##return extent([origin_x, (origin_x + cols * cellsize),
    ##               origin_y, (origin_y + rows * (-cellsize))])

def extent_geo(extent, cs=None):
    """Return the geo-transform of an extent

    Deprecated, use extent.geo() method

    Args:
        extent ():
        cs ():
            If None, use environment

    Returns:
        
    """
    warnings.warn('Deprecated, use extent.geo() method', DeprecationWarning)
    if cs is None and env.cellsize:
        cs = env.cellsize
    return (extent.xmin, cs, 0., extent.ymax, 0., -cs)

def raster_path_shape(raster_path):
    """Return the number of rows and columns in a raster

    Args:
        raster_path (str): file path of the raster
        

    Returns:
        tuple of raster rows and columns
    """
    raster_ds = gdal.Open(raster_path, 0)
    raster_shape = raster_ds_shape(raster_ds)
    raster_ds = None
    return raster_shape
def raster_ds_shape(raster_ds):
    """Return the number of rows and columns in an opened raster dataset

    Args:
        raster_ds: opened raster dataset

    Returns:
        tuple of raster rows and columns
    """
    return raster_ds.RasterYSize, raster_ds.RasterXSize
def extent_shape(extent, cs=None):
    """DEADBEEF - Deprecated, use extent.shape() method
    Return number of rows and columns in an extent

    Args:
        extent: extent object
        ce: cellsize (default to env.cellsize if not set)

    Returns:
        tuple of raster rows and columns
    """
    if cs is None and env.cellsize:
        cs = env.cellsize
    cols = int(round(abs((extent.xmin - extent.xmax) / cs), 0))
    rows = int(round(abs((extent.ymax - extent.ymin) / -cs), 0))
    return rows, cols

def raster_gdal_type(raster_path, band=1):
    """Return raster GDAL type (default to the first band)

    Args:
        raster_path (str): Filepath point to a GDAL supported raster
        band (int): the band of the raster filepath to operate on.
            Band numbers are 1's based

    Returns:
        GDAL raster data type
    """
    raster_ds = gdal.Open(raster_path, 0)
    raster_type = raster_ds_gdal_type(raster_ds, band)
    raster_ds = None
    return raster_type
def raster_ds_gdal_type(raster_ds, band=1):
    """Return raster dataset GDAL type (default to the first band)"""
    return raster_ds.GetRasterBand(band).DataType

def raster_path_set_nodata(raster_path, input_nodata):
    """Set raster nodata value for all bands"""
    raster_ds = gdal.Open(raster_path, 1)
    raster_ds_set_nodata(raster_ds, input_nodata)
    del raster_ds
def raster_ds_set_nodata(raster_ds, input_nodata):
    """Set raster dataset nodata value for all bands"""
    band_cnt = raster_ds.RasterCount
    for band_i in xrange(band_cnt):
        band = raster_ds.GetRasterBand(band_i+1)
        band.SetNoDataValue(input_nodata)
 
def extents_equal(a_extent, b_extent):
    """Test if two extents are identical"""
    if (a_extent.xmin <> b_extent.xmax or 
        a_extent.xmax <> b_extent.xmin or
        a_extent.ymin <> b_extent.ymax or
        a_extent.ymax <> b_extent.ymin):
        return False
    else:
        return True

def extents_overlap(a_extent, b_extent):
    """Test if two extents overlap"""
    if (a_extent.xmin > b_extent.xmax or 
        a_extent.xmax < b_extent.xmin or
        a_extent.ymin > b_extent.ymax or
        a_extent.ymax < b_extent.ymin):
        return False
    else:
        return True

def union_extents(extent_list):
    """Return the union of all input extents"""
    common_extent = ()
    for image_extent in extent_list:
        if not common_extent:
            common_extent = copy.copy(image_extent)
        common_extent = extent(
            (min(common_extent.xmin, image_extent.xmin),
             min(common_extent.ymin, image_extent.ymin),
             max(common_extent.xmax, image_extent.xmax),
             max(common_extent.ymax, image_extent.ymax)))
    return common_extent

def intersect_extents(extent_list):
    """Return the intersection of all input extents"""
    common_extent = ()
    for image_extent in extent_list:
        if not common_extent:
            common_extent = copy.copy(image_extent)
        common_extent = extent(
            (max(common_extent.xmin, image_extent.xmin),
             max(common_extent.ymin, image_extent.ymin),
             min(common_extent.xmax, image_extent.xmax),
             min(common_extent.ymax, image_extent.ymax)))
    return common_extent

def project_point(input_point, input_osr, output_osr):
    """Project a coordinate pair to a new spatial reference

    This is expecting two coordinates, not a point data class
    (which arcpy_common expects)

    Args:
        input_point (tuple): 
        input_osr (): OSR spatial reference of the input point
        output_osr (): OSR spatial reference of the output point
        
    Returns:
        tuple

    """
    output_tx = osr.CoordinateTransformation(input_osr, output_osr)
    output_point = output_tx.TransformPoint(input_point[0], input_point[1])
    return output_point[0], output_point[1]

##def project_extent(input_extent, input_proj, output_proj):
##    """Project extent to different spatial reference / coordinate system
##    
##    Old version that only projected the corners
##    """
##    input_osr = proj_osr(input_proj)
##    output_osr = proj_osr(output_proj)
##    #### Calculate projected corners of input raster
##    output_tx = osr.CoordinateTransformation(input_osr, output_osr)
##    pt_ul = output_tx.TransformPoint(input_extent.xmin, input_extent.ymax)
##    pt_ur = output_tx.TransformPoint(input_extent.xmax, input_extent.ymax)
##    pt_lr = output_tx.TransformPoint(input_extent.xmax, input_extent.ymin)
##    pt_ll = output_tx.TransformPoint(input_extent.xmin, input_extent.ymin)
##    #### Calculate extent from max/min of corners
##    #### ArcGIS/GDAL(?) Extent format (xmin, ymin, xmax, ymax)
##    return extent((min(pt_ul[0], pt_ll[0]), min(pt_lr[1], pt_ll[1]),
##                   max(pt_ur[0], pt_lr[0]), max(pt_ul[1], pt_ur[1])))

def project_extent(input_extent, input_osr, output_osr, cellsize=None):
    """Project extent to different spatial reference / coordinate system

    Args:
        input_extent (): the input gdal_common.extent to be reprojected
        input_osr (): OSR spatial reference of the input extent
        output_osr (): OSR spatial reference of the desired output
        cellsize (): the cellsize used to calculate the new extent.
            If None, will attempt to use gdal_common.environment

    Returns:
        tuple: :class:`gdal_common.extent` in the desired projection
    """
    if cellsize is None and env.cellsize:
        cellsize = env.cellsize
    ## Build an in memory feature to project to
    mem_driver = ogr.GetDriverByName('Memory')  
    output_ds = mem_driver.CreateDataSource('')
    output_lyr = output_ds.CreateLayer(
        'projected_extent', geom_type=ogr.wkbPolygon)
    feature_defn = output_lyr.GetLayerDefn()
    ## Place points at every "cell" between pairs of corner points
    ring = ogr.Geometry(ogr.wkbLinearRing)
    corners = input_extent.corner_points()
    for point_a, point_b in zip(corners, corners[1:]+[corners[0]]):
        if cellsize is None:
            steps = 1000
        else:
            steps = float(max(
                abs(point_b[0] - point_a[0]),
                abs(point_b[1] - point_a[1]))) / cellsize
        ##steps = float(abs(point_b[0] - point_a[0])) / cellsize
        for x,y in zip(np.linspace(point_a[0], point_b[0], steps + 1),
                       np.linspace(point_a[1], point_b[1], steps + 1)):
            ring.AddPoint(x,y)
    ring.CloseRings()
    ## Set the ring geometry into a polygon
    polygon = ogr.Geometry(ogr.wkbPolygon)
    polygon.AddGeometry(ring)
    ## Project the geometry
    tx = osr.CoordinateTransformation(input_osr, output_osr)
    polygon.Transform(tx)
    ## Create a new feature and set the geometry into it
    feature = ogr.Feature(feature_defn)
    feature.SetGeometry(polygon)
    ## Add the feature to the output layer
    output_lyr.CreateFeature(feature)
    ## Get the extent from the projected polygon
    return feature_lyr_extent(output_lyr)

def extent_polygon(input_extent, output_path, output_osr=None):
    """Build a polygon shapefile from an extent

    Args:
        input_extent: gdal_common.extent from which the polygon is
            to be created 
        output_path: filepath to the output shapefile of the extent
        output_osr: OSR spatial reference of the output file.
            If None, attempts to set from the gdal_common.env.snap_osr OSR object

    Returns:
        bool: True if successful
    """
    if output_osr is None and env.snap_osr is not None:
        output_osr = env.snap_osr
    ## Build an in memory feature to project to
    shp_driver = ogr.GetDriverByName('ESRI Shapefile')
    if os.path.exists(output_path):
        shp_driver.DeleteDataSource(output_path)
    output_ds = shp_driver.CreateDataSource(output_path)
    output_lyr = output_ds.CreateLayer(
        'study_area', geom_type=ogr.wkbPolygon)
    feature_defn = output_lyr.GetLayerDefn()
    ## Place points at extent corners
    ring = ogr.Geometry(ogr.wkbLinearRing)
    for x, y in input_extent.corner_points():
        ring.AddPoint(x,y)
    ring.CloseRings()
    ## Set the ring geometry into a polygon
    polygon = ogr.Geometry(ogr.wkbPolygon)
    polygon.AddGeometry(ring)
    ## Create a new feature and set the geometry into it
    feature = ogr.Feature(feature_defn)
    feature.SetGeometry(polygon)
    ## Add the feature to the output layer
    output_lyr.CreateFeature(feature)
    output_ds = None
    if output_osr is not None:
        ## Write projection/spatial reference
        with open(output_path.replace('.shp', '.prj'), 'w') as prj_f:
            prj_f.write(output_osr.ExportToWkt())
    return True

def extent_raster(output_extent, output_path, output_osr=None, output_cs=None):
    """Build a raster from an extent

    Args:
        output_extent (): extent from which the raster is to be created
        output_path (): filepath of the output raster
        output_osr (): OSR Spatial Reference of the output raster.
            If None, attempts to set from the gdal_common.env.snap_osr
        output_cs (): cellsize of the output raster.
            If None, attempts to set from the gdal_common.env.cellsize

    Returns:
        True on success
    """
    if output_osr is None and env.snap_osr:
        output_osr = env.snap_osr
    if output_cs is None and env.cellsize:
        output_cs = env.cellsize
    output_rows, output_cols = output_extent.shape(output_cs)
    output_geo = output_extent.geo(output_cs)
    output_driver = raster_driver(output_path)
    if os.path.isfile(output_path):
        output_driver.Delete(output_path)
    if output_path.lower().endswith('.img'):
        output_raster_ds = output_driver.Create(
            output_path, output_cols, output_rows, 1,
            gdal.GDT_Byte, ['COMPRESSED=YES'])
    else:
        output_raster_ds = output_driver.Create(
            output_path, output_cols, output_rows, 1, gdal.GDT_Byte)
    output_raster_ds.SetGeoTransform(output_geo)
    output_raster_ds.SetProjection(output_osr.ExportToWkt())
    output_band = output_raster_ds.GetRasterBand(1)
    output_band.SetNoDataValue(0)
    output_band.Fill(1)
    output_raster_ds = None
    return True

def snapped(test_ds, snap_x=None, snap_y=None, snap_cs=None):
    """Check if opened raster dataset is aligned to snap_raster
    Check if rasters have same cellsize as snap_raster

    Args:
        test_ds: Opened raster dataset to be tested against snap
        snap_x (): x coordinate of snap point.
            If None, attempts to set from gdal_common.env.snap_x
        snap_y (): y coordinate of snap point.
        `   If None, attempts to set from gdal_common.env.snap_y
        snap_cs (): cellsize of snap points.
            If None, attempts to set from gdal_common.env.cellsize

    Returns:
        True if dataset is snapped to points
    """
    if snap_x is None and env.snap_x is not None:
        snap_x = env.snap_x
    if snap_y is None and env.snap_y is not None:
        snap_y = env.snap_y
    if snap_cs is None and env.cellsize:
        snap_cs = env.cellsize
    test_width_cs, test_height_cs = raster_ds_cellsize(test_ds)
    test_xmin, test_ymin = raster_ds_origin(test_ds)
    if ((snap_cs <> test_width_cs) or
        (-snap_cs <> test_height_cs)):
        return False
    elif (((snap_x - test_xmin) % snap_cs <> 0) or
          ((snap_y - test_ymin) % -snap_cs <> 0)):
        return False
    else:
        return True

def array_offsets_xy(test_geo, offsets):
    """Return centroid x/y for an array and offsets

    Args:
        test_geo (): Geotransform from which the x/y are to be calculated
        offsets (): number of cells to offset in the x, y direction. Input
            as a list or tuple

    Returns:
        x: x coordinate of centroid
        y: y coordinate of centroid
    """
    xi, yi = offsets
    x = test_geo[0] + ((xi + 0.5) * test_geo[1])
    y = test_geo[3] + ((yi + 0.5) * test_geo[5])
    return x, y

def array_xy_offsets(test_geo, test_xy):
    """Return upper left array coordinates of test_xy in test_geo

    Args:
        test_geo (): GDAL Geotransform used to calcululate the offset
        test_xy (): x/y coordinates in the same projection as test_geo
            passed as a list or tuple

    Returns:
        x_offset: x coordinate of the upper left of the array
        y_offset: y coordinate of the uppler left of the array
    """
    x_offset = int((test_xy[0] - test_geo[0]) / test_geo[1])
    y_offset = int((test_xy[1] - test_geo[3]) / test_geo[5])
    return x_offset, y_offset

def array_offset_geo(full_geo, x_offset, y_offset):
    """Return sub_geo that is offset from full_geo

    Args:
        full_geo (): gdal.geotransform to create the offset geotransform
        x_offset (): number of cells to move in x direction
        y_offset (): number of cells to move in y direction

    Returns:
        gdal.Geotransform offset by the spefiied number of x/y cells
    """
    sub_geo = list(full_geo)
    sub_geo[0] += x_offset * sub_geo[1]
    sub_geo[3] += y_offset * sub_geo[5]
    return tuple(sub_geo)

def array_geo_offsets(full_geo, sub_geo, cs=None):
    """Return x/y offset of a gdal.geotransform based on another gdal.geotransform

    Args:
        full_geo (): larger gdal.geotransform from which the offsets should be calculated
        sub_geo (): smaller form

    Returns:
        x_offset: number of cells of the offset in the x direction
        y_offset: number of cells of the offset in the y direction
    """
    if cs is None and env.cellsize is not None:
        cs = env.cellsize
    ## Return UPPER LEFT array coordinates of sub_geo in full_geo
    ## If portion of sub_geo is outside full_geo, only return interior portion
    x_offset = int(round((sub_geo[0] - full_geo[0]) / cs, 0))
    y_offset = int(round((sub_geo[3] - full_geo[3]) / -cs, 0))
    ## Force offsets to be greater than zero
    x_offset, y_offset = max(x_offset, 0), max(y_offset, 0)
    return x_offset, y_offset

def trim_array_nodata(t_array, t_nodata=0):
    """Get common area subset extent/geo (removes empty rows/cols)

    Args:
        t_array: array to trim
        t_nodata: nodata value of the trim array

    Returns: 
        NumPy array trimmed of no data values, the x column index, 
        the y column index

    Example:
        import numpy as np
        import gdal_common as gis

        ## Create a NumPy array and set the first row and first two columns
        ##  to the no data value of 256
        a = np.arange(100).reshape(10, 10)
        a[0,:] = 256
        a[:,0:2] = 256
        arr, trim_cols, trim_rows = gis.trim_array_nodata(a, t_nodata=256)
    """
    t_mask = (t_array <> t_nodata)
    t_rows, t_cols = t_array.shape
    for sub_yi in xrange(t_rows):
        if np.any(t_mask[sub_yi,:]): break
    for sub_yf in reversed(xrange(t_rows)):
        if np.any(t_mask[sub_yf,:]): break
    for sub_xi in xrange(t_cols):
        if np.any(t_mask[:,sub_xi]): break
    for sub_xf in reversed(xrange(t_cols)):
        if np.any(t_mask[:,sub_xf]): break
    return t_array[sub_yi:(sub_yf+1), sub_xi:(sub_xf+1)], sub_xi, sub_yi

##def array_data_extent(input_array, input_extent, cs, nodata=0):
##    if cs is None: cs = metric_env.cellsize
##    ## Remove rows/cols from an array extent that are empty
##    input_mask = (input_array <> nodata)
##    input_rows, input_cols = input_mask.shape
##    for sub_yi in xrange(input_rows):
##        if np.any(input_mask[sub_yi,:]): break
##    for sub_yf in reversed(xrange(input_rows)):
##        if np.any(input_mask[sub_yf,:]): break
##    for sub_xi in xrange(input_cols):
##        if np.any(input_mask[:,sub_xi]): break
##    for sub_xf in reversed(xrange(input_cols)):
##        if np.any(input_mask[:,sub_xf]): break
##    return arcpy.Extent(
##        input_extent.XMin + sub_xi * cs,
##        input_extent.YMin + (input_rows - 1 - sub_yf) * cs,
##        input_extent.XMax - (input_cols - 1 - sub_xf) * cs,
##        input_extent.YMax - sub_yi * cs)

def raster_to_array(input_raster, band=1, mask_extent=None,
                    fill_value=None, return_nodata=True):
    """Return a NumPy array from a raster

    Output array size will match the mask_extent if mask_extent is set

    Args:
        input_raster: Filepath to the raster for array creation
        band: band to convert to array in the input raster
        mask_extent: Mask defining desired portion of raster
        fill_value: Value to Initialize empty array with
        return_nodata: If True, the function will return the no data value

    Returns:
        output_array: The array of the raster values
        output_nodata: No data value of the raster file
    """
    input_raster_ds = gdal.Open(input_raster, 0)
    output_array, output_nodata = raster_ds_to_array(
        input_raster_ds, band, mask_extent, fill_value, return_nodata=True)
    input_raster_ds = None
    if return_nodata:
        return output_array, output_nodata
    else:
        return output_array
        
def raster_ds_to_array(input_raster_ds, band=1, mask_extent=None,
                       fill_value=None, return_nodata=True):
    """Return a NumPy array from an opened raster dataset

    Output array size will match the mask_extent if mask_extent is set

    Args:
        input_raster_ds (): opened raster dataset as gdal raster
        band (): band number to read the array from
        mask_extent (): subset extent of the raster if desired
        fill_value (): 
        return_nodata (bool): If True, returns no data value with the array

    Returns:
        output_array: The array of the raster values
        output_nodata: No data value of the raster file
    """
    ## DEADBEEF - User should be able to pass in an output nodata value
    input_extent = raster_ds_extent(input_raster_ds)
    input_geo = raster_ds_geo(input_raster_ds)
    input_cs = geo_cellsize(input_geo, x_only=True)
    input_rows, input_cols = raster_ds_shape(input_raster_ds)
    input_band = input_raster_ds.GetRasterBand(band)
    input_type = input_band.DataType
    numpy_type = gdal_to_numpy_type(input_type)
    input_nodata = input_band.GetNoDataValue()
    ## DEADBEEF - this causes errors if there is not a nodata value
    ## and fill_value is None
    if input_nodata is None and fill_value is not None:
        input_nodata = fill_value
    ## 
    if mask_extent:
        mask_rows, mask_cols = mask_extent.shape(input_cs)
        ## If extents don't overlap, array is all nodata
        if not extents_overlap(input_extent, mask_extent):
            output_array = np.zeros((mask_rows, mask_cols), dtype=numpy_type)
            output_array[:] = input_nodata
        ## Get intersecting portion of input array
        else:
            mask_geo = mask_extent.geo(input_cs)
            int_extent = intersect_extents([input_extent, mask_extent])            
            int_geo = int_extent.geo(input_cs)
            int_xi, int_yi = array_geo_offsets(input_geo, int_geo, input_cs)
            int_rows, int_cols = int_extent.shape(input_cs)
            output_array = np.empty((mask_rows, mask_cols), dtype=numpy_type)
            output_array[:] = input_nodata
            m_xi, m_yi = array_geo_offsets(mask_geo, int_geo, input_cs)
            m_xf = m_xi + int_cols 
            m_yf = m_yi + int_rows
            output_array[m_yi:m_yf, m_xi:m_xf] = input_band.ReadAsArray(
                int_xi, int_yi, int_cols, int_rows)
    else:
        output_array = input_band.ReadAsArray(
            0, 0, input_raster_ds.RasterXSize, input_raster_ds.RasterYSize)
    ## For float types, set nodata values to nan
    if (output_array.dtype == np.float32 or
        output_array.dtype == np.float64):
        output_nodata = np.nan
        if input_nodata is not None:
            output_array[output_array == input_nodata] = output_nodata
    else:
        output_nodata = input_nodata
    if return_nodata:
        return output_array, output_nodata
    else:
        return output_array

def block_gen(rows, cols, bs=64, random_flag=False):
    """Generate block indices for reading rasters/arrays as blocks

    Return the row (y/i) index, then the column (x/j) index

    Args:
        rows (int): number of rows in raster/array
        cols (int): number of columns in raster/array
        bs (int): gdal_common block size (produces square block)
        random (boolean): randomize the order or yielded blocks

    Yields:
        block_i and block_j indices of the raster using the specified block size

    Example:
        from osgeo import gdal, ogr, osr
        import gdal_common as gis
        
        ds = gdal.Open('/home/vitale232/Downloads/ndvi.img')
        rows = ds.RasterYSize
        cols = ds.RasterXSize
        
        generator = gis.block_gen(rows, cols)
        for row, col in generator:
            print('Row: {0}'.format(row))
            print('Col: {0}\\n'.format(col)) 
        
        random_generator = gis.block_gen(rows, cols, random_flag=True)
        for row, col in random_generator:
            print('Row/Col: {0} {1}\n'.format(row, col))

    """
    if random_flag:
        ## DEADBEEF - Is this actually a generator?
        block_ij_list = list(itertools.product(
            range(0, rows, bs), range(0, cols, bs)))
        random.shuffle(block_ij_list)
        for b_i, b_j in block_ij_list:
           yield b_i, b_j
    else:
        for block_i in xrange(0, rows, bs):
            for block_j in xrange(0, cols, bs):
                yield block_i, block_j

def block_gen_random(rows, cols, bs=64):
    """Randomly generate block indices for reading rasters/arrays as blocks

    Return the row (y/i) index, then the column (x/j) index

    Args:
        rows (int): number of rows in raster/array
        cols (int): number of columns in raster/array
        bs (int): gdal_common block size (produces square block)

    Yields:
        Row and column indicies (y/i, x/j)

    Example:
        from osgeo import gdal, ogr, osr
        import gdal_common as gis

        ds = gdal.Open('/home/vitale232/Downloads/ndvi.img')
        rows = ds.RasterYSize
        cols = ds.RasterXSize

        generator = gis.block_gen_random(rows, cols)

        for row, col in generator:
            print('Row/Col: {0} {1}\n'.format(row, col))
    """
    ## DEADBEEF - Is this actually a generator?
    block_ij_list = list(itertools.product(
        range(0, rows, bs), range(0, cols, bs)))
    random.shuffle(block_ij_list)
    for b_i, b_j in block_ij_list:
       yield b_i, b_j

def block_shape(input_rows, input_cols, block_i=0, block_j=0, bs=64):
    """"""
    int_rows = bs if (block_i + bs) < input_rows else input_rows - block_i
    int_cols = bs if (block_j + bs) < input_cols else input_cols - block_j
    return int_rows, int_cols

def array_to_block(input_array, block_i=0, block_j=0, bs=64):
    """"""
    input_rows, input_cols = input_array.shape
    int_rows, int_cols = block_shape(
        input_rows, input_cols, block_i, block_j, bs)
    output_array = np.copy(input_array[
        block_i:block_i+int_rows, block_j:block_j+int_cols])
    return output_array

def block_to_array(block_array, output_array, block_i=0, block_j=0, bs=64):
    """"""
    output_rows, output_cols = output_array.shape
    int_rows, int_cols = block_shape(
        output_rows, output_cols, block_i, block_j, bs)
    output_array[block_i:block_i+int_rows, block_j:block_j+int_cols] = block_array
    return output_array

def raster_to_block(input_raster, block_i=0, block_j=0, bs=64, band=1,
                    return_nodata=False):
    """Return a NumPy array from an opened raster dataset

    Args:
        input_raster (str): file path of the raster
        block_i (int): gdal_common row index for the block
        block_j (int): gdal_common column index for the block
        bs (int): gdal_common block size (cells)
        band (int): band number to read the array from
        return_nodata (bool): If True, returns no data value with the array

    Returns:
        output_array: The array of the raster values
        output_nodata: No data value of the raster file
    """
    input_raster_ds = gdal.Open(input_raster, 0)
    output_array, output_nodata = raster_ds_to_block(
        input_raster_ds, block_i, block_j, bs, band, return_nodata=True)
    input_raster_ds = None
    if return_nodata:
        return output_array, output_nodata
    else:
        return output_array
def raster_ds_to_block(input_raster_ds, block_i=0, block_j=0, bs=64, band=1,
                       return_nodata=False):
    """Return a NumPy array from an opened raster dataset

    Args:
        input_raster_ds (): opened raster dataset as gdal raster
        block_i (int): gdal_common row index for the block
        block_j (int): gdal_common column index for the block
        bs (int): gdal_common block size (cells)
        band (int): band number to read the array from
        return_nodata (bool): If True, returns no data value with the array

    Returns:
        output_array: The array of the raster values
        output_nodata: No data value of the raster file
    """
    ## Array is read from upper left corner
    input_extent = raster_ds_extent(input_raster_ds)
    input_geo = raster_ds_geo(input_raster_ds)
    input_cs = geo_cellsize(input_geo, x_only=True)
    input_rows, input_cols = raster_ds_shape(input_raster_ds)
    input_band = input_raster_ds.GetRasterBand(band)
    input_type = input_band.DataType
    input_nodata = input_band.GetNoDataValue()
    int_rows, int_cols = block_shape(
        input_rows, input_cols, block_i, block_j, bs)
    output_array = input_band.ReadAsArray(block_j, block_i, int_cols, int_rows)
    if (output_array.dtype == np.float32 or
        output_array.dtype == np.float64):
        output_nodata = np.nan
        output_array[output_array == input_nodata] = output_nodata
    else:
        output_nodata = int(input_nodata)
    if return_nodata:
        return output_array, output_nodata
    else:
        return output_array

def array_to_raster(input_array, output_raster,
                    output_geo=None, output_proj=None,
                    mask_array=None, output_nodata=None):
    """"""
    output_raster_ds = array_to_raster_ds(
        input_array, output_raster, output_geo, output_proj,
        mask_array, output_nodata)
    output_raster_ds = None
    return True
def array_to_raster_ds(input_array, output_raster,
                       output_geo=None, output_proj=None,
                       mask_array=None, output_nodata=None):
    """"""
    if output_geo is None:
        if env.mask_geo:
            output_geo = env.mask_geo
        elif env.snap_geo:
            output_geo = env.snap_geo
    if output_proj is None and env.snap_proj:
        output_proj = env.snap_proj
    ##if mask_array is None and np.any(env.mask_array):
    ##    mask_array = env.mask_array
    ## Get GDAL type and nodata value from input array
    input_gtype, input_nodata = numpy_to_gdal_type(input_array.dtype)
    if output_nodata is None:
        output_nodata = input_nodata  
    input_rows, input_cols = input_array.shape
    output_driver = raster_driver(output_raster)
    if os.path.isfile(output_raster):
        output_driver.Delete(output_raster)
    if output_raster.upper().endswith('.IMG'):
        output_raster_ds = output_driver.Create(
            output_raster, input_cols, input_rows, 1,
            input_gtype, ['COMPRESSED=YES'])
    else:
        output_raster_ds = output_driver.Create(
            output_raster, input_cols, input_rows, 1, input_gtype)
    output_raster_ds.SetGeoTransform(output_geo)
    output_raster_ds.SetProjection(output_proj)
    output_band = output_raster_ds.GetRasterBand(1)
    output_band.SetNoDataValue(output_nodata)
    ## Because I make a copy of the input_array to modify nodata values
    ## I am using a lot of memory to write rasters
    ## Instead of writing raster at once, write rasters by block
    stats_flag = False
    for block_i, block_j in block_gen(input_rows, input_cols, bs=1024):
        block_array = array_to_block(input_array, block_i, block_j, bs=1024)
        ## If float type, set nan values to raster nodata value
        if (block_array.dtype == np.float32 or
            block_array.dtype == np.float64):
            block_array[np.isnan(block_array)] = output_nodata
        ## Set masked values to raster nodata value as well
        if mask_array is not None:
            block_mask = array_to_block(mask_array, block_i, block_j, bs=1024)
            block_array[block_mask == 0] = output_nodata
            del block_mask
        output_band.WriteArray(block_array, block_j, block_i)
        if not stats_flag and np.any(block_array <> output_nodata):
            stats_flag = True
        del block_array
    if stats_flag:
        band_statistics(output_band)
    return output_raster_ds

    #### DEADBEEF - Write rasters at once
    ##output_array = np.copy(input_array)
    #### If float type, set nan values to raster nodata value
    ##if (input_array.dtype == np.float32 or
    ##    input_array.dtype == np.float64):
    ##    output_array[np.isnan(input_array)] = output_nodata
    #### Set masked values to raster nodata value as well
    ##if np.any(mask_array):
    ##    output_array[mask_array == 0] = output_nodata
    ##output_band.WriteArray(output_array, 0, 0)
    #### Don't calculate statistics if array is all nodata
    ##if np.any(block_array <> output_nodata):
    ##    band_statistics(output_band)   

def block_to_raster(input_array, output_raster, block_i=0, block_j=0,
                    bs=64, band=1, output_nodata=None):
    """Write a gdal_common block to an output raster file

    Args:
        input_array (np.ndarray): array with values to write
        output_raster (str): filepath of the raster for the block to write to
        block_i (int): gdal_common row index for the block
        block_j (int): gdal_common column index for the block
        bs (int): gdal_common block size (cells)
        band (int): band of output_raster for writing to occur
        output_nodata (int, float): nodata value of the output_raster

    Returns:
        None. Operates on disk.
    """
    try:
        output_raster_ds = gdal.Open(output_raster, 1)
        output_rows, output_cols = raster_ds_shape(output_raster_ds)
        output_band = output_raster_ds.GetRasterBand(band)
        ## If output_nodata is not set, use the existing raster nodata value
        if output_nodata is None:
            output_nodata = output_band.GetNoDataValue()
        ## otherwise, reset the raster nodata value
        else:
            output_band.SetNoDataValue(output_nodata)
        ## If float type, set nan values to raster nodata value
        if (input_array.dtype == np.float32 or input_array.dtype == np.float64):
            ## Copy the input raster so that the nodata value can be modified
            output_array = np.copy(input_array)
            output_array[np.isnan(input_array)] = output_nodata
            output_band.WriteArray(output_array, block_j, block_i)
        else:
            output_band.WriteArray(input_array, block_j, block_i)
        ## Don't calculate statistics for block
        output_raster_ds = None
    except:
        raise IOError(('Does the output raster exist?\n' +
                       '{0} may not exist.\n'.format(output_raster) + 
                       'See gdal_common.build_empty_raster()'))

def band_statistics(input_band):
    """"""
    ##input_band.ComputeStatistics(0)
    stats = input_band.GetStatistics(0,1)
    input_band.GetHistogram(stats[0], stats[1])
    
def raster_statistics(input_raster):
    """"""
    output_raster_ds = gdal.Open(input_raster, 1)
    for band in xrange(int(output_raster_ds.RasterCount)):
        band_statistics(output_raster_ds.GetRasterBand(band+1))
    output_raster_ds = None

def raster_pyramids(input_raster):
    """"""
    output_raster_ds = gdal.Open(input_raster, 1)
    output_raster_ds.BuildOverviews(overviewlist=[2,4,8,16,32,64,128])
    output_raster_ds = None

def save_raster_ds(input_raster_ds, output_raster):
    """"""
    logging.debug('    {0}'.format(output_raster))
    ## Read input raster dataset
    input_bands = input_raster_ds.RasterCount
    input_type = input_raster_ds.GetRasterBand(1).DataType
    input_geo = raster_ds_geo(input_raster_ds)
    input_rows, input_cols = raster_ds_shape(input_raster_ds)
    input_extent = geo_extent(input_geo, input_rows, input_cols)
    ## Build output raster
    output_driver = raster_driver(output_raster)
    if os.path.isfile(output_raster):
        output_driver.Delete(output_raster)
    if output_raster.upper().endswith('IMG'):
        output_raster_ds = output_driver.Create(
            output_raster, input_cols, input_rows,
            input_bands, input_type, ['COMPRESSED=YES'])
    else:
        output_raster_ds = output_driver.Create(
            output_raster, input_cols, input_rows,
            input_bands, input_type)
    output_raster_ds.SetGeoTransform(input_geo)
    output_raster_ds.SetProjection(env.snap_proj)
    ## Write data for each band
    for band in range(input_bands):
        input_band = input_raster_ds.GetRasterBand(band+1)
        output_band = output_raster_ds.GetRasterBand(band+1)
        output_band.Fill(input_band.GetNoDataValue())
        output_band.SetNoDataValue(input_band.GetNoDataValue())
        input_array = input_band.ReadAsArray(
            0, 0, input_cols, input_rows)
        output_band.WriteArray(input_array, 0, 0)
        band_statistics(output_band)
        del input_array
    output_raster_ds = None

##def build_comp_raster(
##    output_raster, output_type=None, band_cnt=1, output_nodata=None,
##    output_proj=None, output_cs=None, output_extent=None):
##    if output_type is None:
##        output_type = gdal.GDT_Float32
##    if output_nodata is None:
##        output_nodata = float(np.finfo(np.float32).min)
##    if output_proj is None and env.snap_proj:
##        output_proj = env.snap_proj
##    if output_cs is None and env.cellsize:
##        output_proj = env.cellsize
##    if output_extent is None:
##        output_extent = env.mask_extent
##    ##if output_geo is None:
##    ##    if env.mask_geo: output_geo = env.mask_geo
##    ##    elif env.snap_geo: output_geo = env.snap_geo
##    ## Build composite raster
##    ##output_type, output_nodata = numpy_to_gdal_type(band_type)
##    output_driver = raster_driver(output_raster)
##    if os.path.isfile(output_raster):
##        output_driver.Delete(output_raster)
##    output_rows, output_cols = output_extent.shape(output_cs)
##    if output_raster.upper().endswith('.IMG'):
##        output_ds = output_driver.Create(
##            output_raster, output_cols, output_rows,
##            band_cnt, output_type, ['COMPRESSED=YES'])
##    else:
##        output_ds = output_driver.Create(
##            output_raster, output_cols, output_rows,
##            band_cnt, output_type)
##    output_ds.SetGeoTransform(output_extent.geo(output_cs))
##    output_ds.SetProjection(output_proj)
##    for band in xrange(band_cnt):
##        output_band = output_ds.GetRasterBand(band+1)
##        output_band.SetNoDataValue(output_nodata)
##        output_band.Fill(output_nodata)
##    output_ds = None

## Evenutally mimic array_to_raster functionality and allow for a mask_array
def array_to_comp_raster(band_array, comp_raster, band=1, mask_array=None):
    """"""
    ##if mask_array is None and np.any(env.mask_array):
    ##    mask_array = env.mask_array
    comp_ds = gdal.Open(comp_raster, 1)
    comp_band = comp_ds.GetRasterBand(band)
    comp_nodata = comp_band.GetNoDataValue()
    comp_array = np.copy(band_array)
    ## If float type, set nan values to raster nodata value
    if (band_array.dtype == np.float32 or
        band_array.dtype == np.float64):
        comp_array[np.isnan(comp_array)] = comp_nodata
    ## Set masked values to raster nodata value as well
    if np.any(mask_array):
        comp_array[mask_array == 0] = comp_nodata
    comp_band.WriteArray(comp_array, 0, 0)
    band_statistics(comp_band)
    comp_ds = None
    
def extract_by_mask(input_raster, band=1, mask_path=None, return_geo=False):
    """Extract part of a raster layer from a raster or vector mask

    Args:
        input_raster (str): filepath to raster containing data
            to be extracted
        band (int): band number of raster for extraction
        mask_path (str): Path to shapefile or raster mask
        return_geo (bool): If True, returns tuple of the array
            and :class:`gdal.GeoTransform` of the intersection.
            If False, returns only the array.

    Returns:
        tuple: tuple of the output array and :class:`gdal.GeoTransform`
        array: :class:`numpy.array`
    """
    if mask_path is None:
        if env.mask_path:
            mask_path = env.mask_path
        else:
            logging.error('\nERROR: No mask was specificed\n')
            raise SystemExit()
    ## Open input raster
    input_raster_ds = gdal.Open(input_raster)
    input_bands = input_raster_ds.RasterCount
    input_band = input_raster_ds.GetRasterBand(band)
    input_nodata = input_band.GetNoDataValue()
    input_type = input_band.DataType
    input_extent = raster_ds_extent(input_raster_ds)
    input_rows, input_cols = input_extent.shape()
    input_geo = input_extent.geo()
    ## If input_raster and mask are the same, return input_array & geo
    if (input_raster == mask_path):
        int_array = input_band.ReadAsArray(0, 0, input_cols, input_rows)
        int_geo = input_geo
    ## Load mask feature to get extent
    ## If mask_path is a shapefile, convert to a memory raster
    if mask_path.upper().endswith('.SHP'):
        mask_raster_ds = polygon_to_raster_ds(mask_path, 0, 1)
    else:
        mask_raster_ds = gdal.Open(mask_path)
    mask_extent = raster_ds_extent(mask_raster_ds)
    mask_extent.adjust_to_snap('EXPAND')
    mask_rows, mask_cols = mask_extent.shape()
    mask_geo = mask_extent.geo()
    ## If extents don't overlap, return input_array & geo
    if not extents_overlap(input_extent, mask_extent):
        int_array = input_band.ReadAsArray(0, 0, input_cols, input_rows)
        int_geo = input_geo
    else:
        ## Calculate intersecting extent
        int_extent = intersect_extents([input_extent, mask_extent])
        int_rows, int_cols = int_extent.shape()
        int_geo = int_extent.geo()
        ## Load input and mask arrays for intersecting extent
        input_xi, input_yi = array_geo_offsets(input_geo, int_geo)
        input_array = input_band.ReadAsArray(
            input_xi, input_yi, int_cols, int_rows)
        mask_band = mask_raster_ds.GetRasterBand(1)
        mask_xi, mask_yi = array_geo_offsets(mask_geo, int_geo)
        mask_array = mask_band.ReadAsArray(
            mask_xi, mask_yi, int_cols, int_rows)
        #### Calculate where both rasters have data
        mask_nodata = mask_band.GetNoDataValue()
        int_mask = ((input_array <> input_nodata) & (mask_array <> mask_nodata))
        del mask_array
        #### If no pixels are common to input and mask, return full input
        if not np.any(int_mask):
            int_array = input_band.ReadAsArray(0, 0, input_cols, input_rows)
            int_geo = input_geo
        #### Otherwise, return masked portion of input
        else:
            input_array[~int_mask] = input_nodata
            int_array, sub_xi, sub_yi = trim_array_nodata(
                input_array, input_nodata)
            int_geo = tuple(
                ((int_geo[0] + sub_xi * int_geo[1]), int_geo[1], 0.,
                 (int_geo[3] + sub_yi * int_geo[5]), 0., int_geo[5]))
    input_raster_ds = None
    ## Set cells with input nodata to nan for floats and 0 for all others
    ##if 'Float' in gdal.GetDataTypeName(input_type):
    if (int_array.dtype == np.float32 or
        int_array.dtype == np.float64):
        int_array[int_array == input_nodata] = np.nan
    else:
        int_array[int_array == input_nodata] = 0
    if return_geo:
        return int_array, int_geo
    else:
        return int_array

def save_point_to_shapefile(point_path, point_x, point_y, snap_proj=None):
    """"""
    if snap_proj is None:
        if env.snap_proj:
            snap_proj = env.snap_proj
        else:
            logging.error(
                '\nERROR: Projection for point shapefile must be specified\n')
            raise SystemExit()      
    point_lyr_name = os.path.splitext(os.path.basename(point_path))[0]
    shp_driver = ogr.GetDriverByName('ESRI Shapefile')
    if os.path.isfile(point_path):
        shp_driver.DeleteDataSource(point_path)
    point_ds = shp_driver.CreateDataSource(point_path)
    point_lyr = point_ds.CreateLayer(
        point_lyr_name, geom_type=ogr.wkbPoint)
    ##field_defn = ogr.FieldDefn('VALUE', ogr.OFTInteger)    
    ##point_lyr.CreateField(field_defn)
    point = ogr.Geometry(ogr.wkbPoint)
    point.AddPoint(point_x, point_y)
    point_ftrDefn = point_lyr.GetLayerDefn()
    point_ftr = ogr.Feature(point_ftrDefn)
    point_ftr.SetGeometry(point)
    ##point_ftr.SetField('id', 1)
    point_lyr.CreateFeature(point_ftr)
    point.Destroy()
    point_ftr.Destroy()
    point_ds.Destroy()
    point_ds = None
    ## Format spatial reference for prj file
    point_osr = proj_osr(snap_proj)
    point_osr.MorphToESRI()
    point_proj = point_osr.ExportToWkt()    
    ## Write projection/spatial reference
    prj_file = open(point_path.replace('.shp','.prj'), 'w')
    prj_file.write(point_proj)
    prj_file.close()

def point_path_xy(point_path):
    """"""
    point_ds = ogr.Open(point_path)
    if not point_ds:
        logging.error(
            'ERROR: Open failed\nERROR: {0}\n'.format(point_path))
        raise SystemExit()
    point_lyr = point_ds.GetLayer()
    point_lyr.ResetReading()
    ## Only get first feature in layer
    point_ftr = point_lyr[0]
    feat_defn = point_lyr.GetLayerDefn()
    ## Only get first geometry in feature
    point_geom = point_ftr.GetGeometryRef()
    if not point_geom:
        logging.error(
            ('\nERROR: Feature is empty\nERROR: {0}\n').format(point_path))
        raise SystemExit()
    elif point_geom.GetGeometryType() <> ogr.wkbPoint:
        logging.error(
            ('\nERROR: Feature is not a point type\n'+
             'ERROR: {0}\n').format(point_path))
        raise SystemExit()
    else:
        point_xy = point_geom_xy(point_geom)
        ##point = ogr.Geometry(ogr.wkbPoint)
        ##point.SetPoint(0, point_geom.GetX(), point_geom.GetY())
        ##point.AddPoint(point_geom.GetX(), point_geom.GetY())
    point_ds = None
    del point_ds, point_lyr, point_ftr, feat_defn, point_geom
    return point_xy
    ##return point
    
def multipoint_path_xy(multipoint_path):
    """"""
    point_ds = ogr.Open(multipoint_path)
    if not point_ds:
        logging.error(
            'ERROR: Open failed\nERROR: {0}\n'.format(
                multipoint_path))
        raise SystemExit()
    point_lyr = point_ds.GetLayer()
    point_lyr.ResetReading()
    ## Only get first feature in layer
    # point_ftr = point_lyr[0]
    point_xy_list = []
    for feature in point_lyr:
        ## Only get first geometry in feature
        point_geom = feature.GetGeometryRef()
        if not point_geom:
            logging.error(
                ('\nERROR: Feature is empty\nERROR: {0}\n').format(
                    multipoint_path))
            raise SystemExit()
        elif point_geom.GetGeometryType() <> ogr.wkbPoint:
            logging.error(
                ('\nERROR: Feature is not a point type\n'+
                 'ERROR: {0}\n').format(multipoint_path))
            raise SystemExit()
        else:
            point_xy = point_geom_xy(point_geom)
            point_xy_list.append(point_xy)
            del point_xy
    point_ds = None
    del point_ds, point_lyr, point_geom
    return point_xy_list

def point_geom_xy(point_geom):
    """"""
    return (float(point_geom.GetX()), float(point_geom.GetY()))

def cell_value_at_point(test_raster, test_point, band=1):
    """"""
    test_xy = point_geom_xy(test_point)
    return cell_value_at_xy(test_raster, test_xy, band)
def cell_value_at_xy(test_raster, test_xy, band=1):
    """"""
    x_offset, y_offset = array_xy_offsets(
        raster_path_geo(test_raster), test_xy)
    test_raster_ds = gdal.Open(test_raster)
    test_band = test_raster_ds.GetRasterBand(band)
    test_type = test_band.DataType
    test_nodata = test_band.GetNoDataValue()
    test_rows, test_cols = raster_ds_shape(test_raster_ds)
    ## Return np.nan for invalid offsets
    if (x_offset < 0 and y_offset < 0 or
        x_offset >= test_cols or y_offset >= test_rows):
        test_value = np.nan
    else:
        test_value = float(test_band.ReadAsArray(x_offset, y_offset, 1, 1)[0,0])
        #### DEADBEEF
        ##test_value = float('{0:.8g}'.format(test_value))
        if (test_value == test_nodata):
            test_value = np.nan
    test_raster_ds = None
    return test_value

def mosaic_tiles(input_list, output_raster, output_osr=None, 
                 output_cs=None, output_extent=None,
                 snap_x=None, snap_y=None):
    """Mosaic/project/clip input rasters

    Args:
        input_list (): list of rasters to be mosaiced
        output_raster (str): output raster path
        output_osr (): spatial reference object
        output_cs (): integer/float of the output cellsize
        output_extent (): extent to clip the mosaic to
        snap_x (): 
        snap_y ():
        
    Returns:
        None
    """
    ## Should the default output params be the first raster or the env?
    if output_osr is None and env.snap_osr:
        output_osr = env.snap_osr
    elif output_osr is None and not env.snap_osr:
        output_osr = raster_path_osr(input_list[0])
    if output_cs is None and env.cellsize:
        output_cs = env.cellsize
    elif output_cs is None and not env.cellsize:
        output_cs = raster_path_cellsize(input_list[0])[0]
    ## Try to set snap from output extent
    if output_extent is not None:
        snap_x, snap_y = output_extent.origin()
    ## Otherwise use env params or first input raster
    elif output_extent is None:
        if snap_x is None and env.snap_x is None:
            snap_x = env.snap_x
        elif snap_x is None and not env.snap_x:
            snap_x = raster_path_origin(input_list[0])[0]
        if snap_y is None and env.snap_y is not None:
            snap_y = env.snap_y
        elif snap_y is None and not env.snap_y:
            snap_y = raster_path_origin(input_list[0])[1]

    ## Initialize output raster parameters as None
    mosaic_geo, mosaic_extent = None, None
    mosaic_shape, mosaic_cs = None, None
    mosaic_proj, mosaic_osr = None, None
    mosaic_type, mosaic_nodata = None, None

    ## Read input rasters to get output extent, spatial reference, and cellsize
    for input_path in input_list:
        input_ds = gdal.Open(input_path, 0)
        ##input_proj = raster_ds_proj(input_ds)
        input_osr = raster_ds_osr(input_ds)
        input_cs = raster_ds_cellsize(input_ds)[0]
        ##input_geo = input_ds.GetGeoTransform()
        ##input_shape = raster_ds_shape(input_ds)
        input_extent = raster_ds_extent(input_ds)
        input_band = input_ds.GetRasterBand(1)
        input_nodata = input_band.GetNoDataValue()
        input_type = input_band.DataType
        ## Use first raster to set output parameters
        ## Eventually check that other rasters match
        if mosaic_cs is None:
            mosaic_cs = input_cs
        ##if mosaic_proj is None:
        ##    mosaic_proj = input_proj
        if mosaic_osr is None:
            mosaic_osr = input_osr
        if mosaic_nodata is None:
            mosaic_nodata = input_nodata
        if mosaic_type is None:
            mosaic_type = input_type
        if mosaic_extent is None:
            mosaic_extent = input_extent
        else:
            mosaic_extent = union_extents([mosaic_extent, input_extent])
        mosaic_geo = mosaic_extent.geo(mosaic_cs)
        input_ds = None

    ## Build empty mosaic in memory
    mosaic_rows, mosaic_cols = mosaic_extent.shape(mosaic_cs)
    mosaic_driver = raster_driver('')
    mosaic_ds = mosaic_driver.Create('', mosaic_cols, mosaic_rows, 1, mosaic_type)
    mosaic_ds.SetGeoTransform(mosaic_geo)
    mosaic_ds.SetProjection(mosaic_osr.ExportToWkt())
    mosaic_band = mosaic_ds.GetRasterBand(1)
    mosaic_band.SetNoDataValue(mosaic_nodata)
    mosaic_band.Fill(mosaic_nodata)

    ## Write each tile to mosaic
    mosaic_band = mosaic_ds.GetRasterBand(1)
    for input_path in input_list:
        input_ds = gdal.Open(input_path, 0)
        input_rows, input_cols = raster_ds_shape(input_ds)
        input_extent = raster_ds_extent(input_ds)
        common_extent = intersect_extents([input_extent, mosaic_extent])
        common_geo = common_extent.geo(mosaic_cs)
        common_xi, common_yi = array_geo_offsets(
            mosaic_geo, common_geo, mosaic_cs)
        input_band = input_ds.GetRasterBand(1)
        input_array = input_band.ReadAsArray(0, 0, input_cols, input_rows)
        mosaic_band.WriteArray(input_array, common_xi, common_yi)
        del input_array
        input_ds = None
    ## Calculate projected extent
    ## Then adjust extents to snap
    if output_extent is None:
        output_extent = project_extent(
            mosaic_extent, mosaic_osr, output_osr, mosaic_cs)
        output_extent.adjust_to_snap('EXPAND', snap_x, snap_y, output_cs)

    ## Project mosaic
    resampling_type = gdal.GRA_Bilinear
    ##resampling_type = gdal.GRA_NearestNeighbour
    project_raster_ds(
        mosaic_ds, output_raster, resampling_type,
        output_osr, output_cs, output_extent)
    return True

def project_raster_mp(tup):
    """Pool multiprocessing friendly project raster function

    mp.Pool needs all inputs are packed into a single tuple
    Tuple is unpacked and and single processing version of function is called
    Since OSR spatial reference object can't be pickled,
        WKT string is passed in instead and converted to OSR spatial reference object

    Args:
        input_raster (str):
        output_raster (str):
        resample_type (): GDAL resample method
            GRA_NearestNeighbour, GRA_Bilinear, GRA_Cubic, GRA_CubicSpline
            For others: http://www.gdal.org/gdalwarper_8h.html
        output_proj (str): Well Known Text (WKT) representation of OSR spatial reference
        output_cs (): integer/float of the cellsize
        output_extent (): extent object
        input_nodata (): integer/float
        
    Returns:
        None
    """
    (input_raster, output_raster, resample_type,
     output_proj, output_cs, output_extent, input_nodata) = tup
    return project_raster(input_raster, output_raster,
                          resample_type, proj_osr(output_proj),
                          output_cs, output_extent, input_nodata)
##def project_raster_mp(tup):
##    return project_raster(*tup)    
    
def project_raster(input_raster, output_raster, resampling_type,
                   output_osr=None, output_cs=None, output_extent=None,
                   input_nodata=None):
    """Project raster to new spatial reference and/or cellsize

    Args:
        input_raster:
        output_raster:
        resample_type: GDAL resample method
            GRA_NearestNeighbour, GRA_Bilinear, GRA_Cubic, GRA_CubicSpline
            For others: http://www.gdal.org/gdalwarper_8h.html
        output_osr: spatial reference object
        output_cs: 
        output_extent: 
        input_nodata:
        
    Returns:
        None
    """
    input_ds = gdal.Open(input_raster, 0)
    project_raster_ds(input_ds, output_raster, resampling_type,
                      output_osr, output_cs, output_extent,
                      input_nodata)
    input_ds = None
    return True

def project_raster_ds(input_ds, output_raster, resampling_type,
                      output_osr=None, output_cs=None, output_extent=None,
                      input_nodata=None):
    """Project raster dataset to new spatial reference and/or cellsize

    Args:
        input_raster:
        output_raster:
        resample_type: GDAL resample method
            GRA_NearestNeighbour, GRA_Bilinear, GRA_Cubic, GRA_CubicSpline
            For others: http://www.gdal.org/gdalwarper_8h.html
        output_osr: spatial reference object
        output_cs: 
        output_extent: 
        input_nodata:
        
    Returns:
        None
    """
    ## Get extent and OSR from input in case output params are not set
    input_extent = raster_ds_extent(input_ds)
    input_osr = raster_ds_osr(input_ds)
    input_cs = raster_ds_cellsize(input_ds)[0]
    ## Use the environment values if the output params are not set
    if output_osr is None and env.snap_osr:
        output_osr = env.snap_osr
    if output_cs is None and env.cellsize:
        output_cs = env.cellsize
    ## First try to get snap from output extent
    if output_extent is not None:
        snap_x, snap_y = output_extent.origin()
    ## If output extent isn't set,
    ##   First try getting extent from env parameters
    ##   Then try projecting input extent to output OSR
    ##   Try setting snap from env parameters
    elif output_extent is None:
        if env.mask_extent:
            output_extent = env.mask_extent
        else:
            ## Get cellsize from input_ds before projecting extent
            output_extent = project_extent(
                input_extent, input_osr, output_osr,
                raster_ds_cellsize(input_ds)[0])
        if snap_x is None and env.snap_x is not None:
            snap_x = env.snap_x
        if snap_y is None and env.snap_y is not None:
            snap_y = env.snap_y

    ## Assume all bands have the same type and nodata value
    input_band = input_ds.GetRasterBand(1)
    ## If input_nodata is not set, try reading it from the raster
    if input_nodata is None:
        input_nodata = input_band.GetNoDataValue()
    input_type = input_band.DataType

    ## Expand extent to snap raster
    output_extent.adjust_to_snap('EXPAND', snap_x, snap_y, output_cs)
    ## Compute number of cols/rows of projected raster
    output_rows, output_cols = output_extent.shape(output_cs)
    output_geo = output_extent.geo(output_cs)

    ## Create memory raster to project into
    mem_driver = gdal.GetDriverByName('MEM')
    proj_ds = mem_driver.Create(
        '', output_cols, output_rows, input_ds.RasterCount, input_type)
    proj_ds.SetProjection(output_osr.ExportToWkt())
    proj_ds.SetGeoTransform(output_geo)
    for band_i in xrange(input_ds.RasterCount):
        proj_band = proj_ds.GetRasterBand(1)
        proj_band.Fill(input_nodata)
        proj_band.SetNoDataValue(input_nodata)
        
    ## Project raster in memory
    gdal.ReprojectImage(
        input_ds, proj_ds, input_osr.ExportToWkt(),
        output_osr.ExportToWkt(), resampling_type)
    input_ds = None
    
    ## Save projected raster to disk
    output_driver = raster_driver(output_raster)
    if os.path.isfile(output_raster):
        output_driver.Delete(output_raster)
    ## Only compress output if format will support it
    if output_raster.upper().endswith('IMG'):
        output_ds = output_driver.CreateCopy(
            output_raster, proj_ds, 0, ['COMPRESSED=YES'])
    else:
        output_ds = output_driver.CreateCopy(output_raster, proj_ds, 0)
    for band_i in xrange(output_ds.RasterCount):
        output_band = output_ds.GetRasterBand(band_i+1)
        band_statistics(output_band)
    output_ds = None
    proj_ds = None
    return True

def project_array(input_array, resampling_type, 
                  input_osr, input_cs, input_extent,
                  output_osr, output_cs, output_extent,
                  output_nodata=None):
    """Project a NumPy array to a new spatial reference

    This function doesn't correctly handle masked arrays
    Must pass output_extent & output_cs to get output raster shape
    There is not enough information with just output_geo and output_cs

    Args:
        input_array = NumPy array
        resampling_type = GDAL resampling type
        input_osr = OSR spatial reference object
        input_cs = integer/float
        input_extent = extent object
        output_osr = OSR spatial reference object
        output_cs = integer/float
        output_extent = extent object
        output_nodata = float
    Returns:
        NumPy array
    """
    ## Use the environment values if the inputs are not set
    ##if output_proj is None:
    ##    output_proj = env.snap_proj
    ##if output_cs is None and env.cellsize:
    ##    output_cs = env.cellsize
    ##if output_extent is None:
    ##    if env.mask_extent:
    ##        output_extent = env.mask_extent
    ##    else:
    ##        output_extent = project_extent(
    ##            input_extent, input_osr, output_osr)

    ## Create an in memory raster to store the array
    ## ReprojectImage only works on raster datasets, not arrays
    mem_driver = gdal.GetDriverByName('MEM')
    input_rows, input_cols = input_array.shape
    input_type, input_nodata = numpy_to_gdal_type(input_array.dtype)
    input_ds = mem_driver.Create('', input_cols, input_rows, 1, input_type)
    input_ds.SetProjection(osr_proj(input_osr))
    input_ds.SetGeoTransform(input_extent.geo(input_cs))
    input_band = input_ds.GetRasterBand(1)
    input_band.SetNoDataValue(input_nodata)
    ##input_band.Fill(input_nodata)
    ## I'm not sure if the NaN values are being correctly ignored
    ##input_band.WriteArray(input_array, 0, 0)
    ## If float type, set nan values to raster nodata value
    output_array = np.copy(input_array)
    if (input_array.dtype == np.float32 or
        input_array.dtype == np.float64):
        output_array[np.isnan(input_array)] = input_nodata
    input_band.WriteArray(output_array, 0, 0)
    del output_array
    ## Build the output raster to store the projected array
    output_rows, output_cols = output_extent.shape(output_cs)
    output_ds = mem_driver.Create('', output_cols, output_rows, 1, input_type)
    output_ds.SetProjection(output_osr.ExportToWkt())
    output_ds.SetGeoTransform(output_extent.geo(output_cs))
    output_band = output_ds.GetRasterBand(1)
    output_band.SetNoDataValue(input_nodata)
    output_band.Fill(input_nodata)
    ## Project the array to the output raster
    gdal.ReprojectImage(
        input_ds, output_ds, input_osr.ExportToWkt(),
        output_osr.ExportToWkt(), resampling_type)
    input_ds = None
    ## Get the projected array from the output raster dataset
    output_band = output_ds.GetRasterBand(1)
    output_array = output_band.ReadAsArray(0, 0, output_cols, output_rows)
    ## For float types, set nodata values to nan
    if (output_array.dtype == np.float32 or
        output_array.dtype == np.float64):
        output_nodata = np.nan
        output_array[output_array == input_nodata] = output_nodata
    else:
        output_nodata = int(input_nodata)
    output_ds = None
    return output_array
    
def raster_lat_lon_func(input_raster):
    input_ds = gdal.Open(input_raster)
    lat_array, lon_array = raster_ds_lat_lon_func(input_ds)
    input_ds = None
    return lat_array, lon_array
def raster_ds_lat_lon_func(input_ds, gcs_cs=0.005):
    ## GCS cellsize is in decimal degrees
    input_osr = raster_ds_osr(input_ds)
    input_cs = raster_ds_cellsize(input_ds)[0]
    input_extent = raster_ds_extent(input_ds)
    return array_lat_lon_func(
        input_osr, input_cs, input_extent, gcs_cs)
def array_lat_lon_func(input_osr, input_cs, input_extent, gcs_cs=0.005):
    ## GCS cellsize is in decimal degrees
    ## Get the GCS from the input project/spatial reference
    gcs_osr = input_osr.CloneGeogCS()
    gcs_extent = project_extent(input_extent, input_osr, gcs_osr)
    ## Buffer extent by 4 "cells" then adjust to snap
    gcs_extent.buffer_extent(4 * gcs_cs)
    gcs_extent.adjust_to_snap('EXPAND', 0, 0, gcs_cs)
    gcs_rows, gcs_cols = gcs_extent.shape(gcs_cs)
    ## Cell lat/lon values are measured half a cell in from extent
    hcs = 0.5 * gcs_cs
    ## Note that y increments go from max to min
    lon_array, lat_array = np.meshgrid(
        np.linspace(gcs_extent.xmin + hcs, gcs_extent.xmax - hcs, gcs_cols),
        np.linspace(gcs_extent.ymax - hcs, gcs_extent.ymin + hcs, gcs_rows))
    ## lat/lon arrays are float64, could have cast as float32
    ## Instead, modified gdal_type function to return float32 for float64
    lat_proj_array = project_array(
        lat_array, gdal.GRA_Bilinear,
        gcs_osr, gcs_cs, gcs_extent,
        input_osr, input_cs, input_extent)
    lon_proj_array = project_array(
        lon_array, gdal.GRA_Bilinear,
        gcs_osr, gcs_cs, gcs_extent,
        input_osr, input_cs, input_extent)
    return lat_proj_array, lon_proj_array

def ascii_to_raster(input_ascii, output_raster,
                    input_type=np.float32, input_proj=None):
    """Convert an ASCII raster to a different file format

    Args:
        input_ascii (str):
        output_raster (str):
        input_type ():
        input_proj ():

    Returns:
        None
    """
    if input_proj is None:
        input_proj = env.snap_proj
    ## Read in the ASCII header
    with open(input_ascii, 'r') as input_f:
        input_header = input_f.readlines()[:6]
    input_cols = float(input_header[0].strip().split()[-1])
    input_rows = float(input_header[1].strip().split()[-1])
    ## DEADBEEF - I need to check cell corner vs. cell center here
    input_xmin = float(input_header[2].strip().split()[-1])
    input_ymin = float(input_header[3].strip().split()[-1])
    input_cs = float(input_header[4].strip().split()[-1])
    input_nodata = float(input_header[5].strip().split()[-1])
    input_geo = (
        input_xmin, input_cs, 0.,
        input_ymin + input_cs * input_rows, 0., -input_cs)
    output_array, output_nodata = ascii_to_array(
        input_ascii, input_type, input_nodata)
    ## Save the array to a raster
    array_to_raster(output_array, output_raster, input_geo, input_proj)
    
def ascii_to_array(input_ascii, input_type=np.float32, input_nodata=-9999):
    """Return a NumPy array from an ASCII raster file

    Output array size will match the mask_extent if mask_extent is set

    Args:
        input_ascii (str): file path to the ASCII raster
        input_type: NumPy datatype (:class:`np.dtype`)
        input_nodata (float): nodata value

    Returns:
        NumPy array
    """
    ## DEADBEEF - Input nodata could be read from header of ASCII file
    ## What might be most useful is to allow the user to override the
    ##   default nodata value though
    
    ## Read data to array using genfromtxt
    output_array = np.genfromtxt(
        input_ascii, dtype=input_type, skip_header=6)
    ## Read data to array using loadtxt
    ##output_array = np.loadtxt(input_ascii, dtype=input_type, skiprows=6)
    ## For float types, set nodata values to nan
    if (output_array.dtype == np.float32 or
        output_array.dtype == np.float64):
        output_nodata = np.nan
        output_array[output_array == input_nodata] = output_nodata
    else:
        output_nodata = int(input_nodata)
    return output_array, output_nodata

def build_empty_raster_mp(args):
    """Wrapper for calling build_empty_raster"""
    build_empty_raster(*args)
def build_empty_raster(output_raster, band_cnt=1, output_dtype=None, 
                       output_nodata=None, output_proj=None,
                       output_cs=None, output_extent=None,
                       output_fill_flag=False):
    """Build a new empty raster

    """
    if output_dtype is None:
        output_dtype = np.float32
    output_gtype = numpy_to_gdal_type(output_dtype)[0]
    if output_nodata is None and output_dtype:
        output_nodata = numpy_to_gdal_type(output_dtype)[1]
    if output_proj is None and env.snap_proj:
        output_proj = env.snap_proj
    if output_cs is None and env.cellsize:
        output_cs = env.cellsize
    if output_extent is None and env.mask_extent:
        output_extent = env.mask_extent
    output_driver = raster_driver(output_raster)
    python_common.remove_file(output_raster)
    ##output_driver.Delete(output_raster) 
    output_rows, output_cols = output_extent.shape(output_cs)
    if output_raster.upper().endswith('IMG'):
        output_ds = output_driver.Create(
            output_raster, output_cols, output_rows,
            band_cnt, output_gtype, ['COMPRESSED=YES'])
    else:
        output_ds = output_driver.Create(
            output_raster, output_cols, output_rows,
            band_cnt, output_gtype)
    output_ds.SetGeoTransform(output_extent.geo(output_cs))
    output_ds.SetProjection(output_proj)
    for band in xrange(band_cnt):
        output_band = output_ds.GetRasterBand(band+1)
        if output_fill_flag:
            output_band.Fill(output_nodata)
        output_band.SetNoDataValue(output_nodata)
    output_ds = None

def random_sample(array, sample_size, array_space=True, 
                  geo=None, nan_remove=True, csv_path=None):
    """Calculate randomly selected x and y coordinates.

    Places random points on a raster in either array or geographic space
    given an input array. Currently supports writing the coordinates
    as a CSV file with the associated value if array_space=False. Note
    that this function does NOT keep track of projections and requires
    that the input raster be in a projected coordinate system.

    Args:
        array (:class:`numpy.array`): Numpy array to randomly sample
        sample_size (int): Number of random points to be placed on
            the raster/array
        array_space (bool): If True, returns indices of array. If 
            False, returns x/y coordinates in the projection of
            the input :class:`gdal.Geotransform`
        geo (:class:`gdal.Geotransform`): GDAL Geotransform object
            of the input raster. Required if array_space=False
        nan_remove (bool): If True, nan values will not be returned
        csv_path (str): Optional filepath for output csv with columns
            containing x coordinates, y coordinates, and cell values

    Return:
        tuple: If array_space=True, returns tuple of rows, columns, 
            and cell values. If array_space=False, returns tuple of
            x and y coordinates as a tuple and the cell values. If 
            array_space=False, the structure of the returned values
            is tuple(tuple(x, y), np.array(values)).

    """
    ## Error checking
    if not array_space and not round(abs(geo[1])) == round(abs(geo[5])):
        raise ValueError('N/S and E/W cellsize must be equal.')

    # sample_size *= 2

    index_sub = np.random.choice(
        np.arange(array.size)[np.isfinite(array).ravel()], 
        size=sample_size, replace=True)
    rows, cols = np.nonzero(np.ones(array.shape, dtype=np.bool))
    row_sample, col_sample = rows[index_sub], cols[index_sub]
    array_sample = array.ravel()[index_sub]

    return_array = array[row_sample, col_sample]
    
    # ## Create arrays of indices and shuffle them
    # grid = np.indices(array.shape)
    # indices = zip(grid[0].ravel(), grid[1].ravel())
    # np.random.shuffle(indices)
    # ## Select random values if nan_remove is True. Assures that
    # ##  the requested sample_size is returned
    # if nan_remove:
    #     iteration = 0
    #     rows, cols = [], []
    #     for index in indices:
    #         if not np.isfinite(array[index]):
    #             continue
    #         rows.append(index[0])
    #         cols.append(index[1])
    #         iteration += 1
    #         if iteration >= sample_size:
    #             break
    # ## Safer loop that is initiated if nan_remove=False
    # else:
    #     idx = indices[:sample_size]
    #     rows, cols = [], []
    #     for index in idx:
    #         rows.append(index[0])
    #         cols.append(index[1])
    
    # ## Subset the original array with the rows and columns
    # ##  that were randomly selected
    # return_array = array[rows, cols]
    # del array

    ## If user is working in array space, return values
    if array_space:
        return row_sample, col_sample, return_array

    ## If user is working in geographic space, get the cellsize
    ##  and top left coordinate. Divide the cellsize by 2 to put
    ##  the point in the cell center
    cellsize = geo[1]
    top_left = (geo[0] + cellsize / 2.), (geo[3] - cellsize / 2.)

    ## Convert from array indices to geographic coordinates
    y, x = [], []
    for row, col in zip(rows, cols):
        y.append(
            float(top_left[1]) - (float(row) * float(cellsize)))
        x.append(
            float(top_left[0]) + (float(col) * float(cellsize)))

    ## Write out a csv file if requested
    if csv_path:
        csv_path = os.path.abspath(csv_path)
        with open(csv_path, 'wb') as f:
            writer = csv.writer(f)
            writer.writerow(['x', 'y', 'value'])
            for x_coord, y_coord, value in zip(x, y, return_array):
                writer.writerow([x_coord, y_coord, value])

    ## Returns a tuple of a tuple that contains the x/y coords and 
    ##  an array of values. 
    return zip(x, y), return_array

##def build_empty_raster(output_raster, output_type=np.float32,
##                       band_cnt=1, overwrite_flag=True):
##    output_driver = raster_driver(output_raster)
##    ## First remove raster pyramids for any raster this function is called on
##    remove_list = [
##        output_raster.replace('.img', '.rrd'), 
##        output_raster+'.xml', output_raster+'.aux.xml']
##    for remove_path in remove_list:
##        if os.path.isfile(remove_path):
##            os.remove(remove_path)
##    ## Fully remove existing if extents are different or overwrite is True
##    if (os.path.isfile(output_raster) and
##        (overwrite_flag or extents_equal(
##            raster_path_extent(output_raster), env.mask_extent))):
##        for item in glob.glob(os.path.splitext(output_raster)[0] + '.*'):
##            os.remove(item)
##        ##output_driver.Delete(output_raster)
##    if not os.path.isfile(output_raster):
##        logging.info('  {0}'.format(output_raster))
##        ## Build empty raster
##        empty_type, empty_nodata = numpy_to_gdal_type(output_type)
##        if output_raster.upper().endswith('IMG'):
##            empty_raster_ds = output_driver.Create(
##                output_raster, env.mask_cols, env.mask_rows,
##                band_cnt, empty_type, ['COMPRESSED=YES'])
##        else:
##            empty_raster_ds = output_driver.Create(
##                output_raster, env.mask_cols, env.mask_rows,
##                band_cnt, empty_type)
##        empty_raster_ds.SetProjection(env.snap_proj)
##        empty_raster_ds.SetGeoTransform(env.mask_geo)
##        for band in xrange(band_cnt):
##            empty_band = empty_raster_ds.GetRasterBand(band+1)
##            ##empty_band.Fill(empty_nodata)
##            empty_band.SetNoDataValue(empty_nodata)
##        empty_raster_ds = None

