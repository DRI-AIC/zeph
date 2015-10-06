from __future__ import division, print_function, unicode_literals
import os
import sys

import numpy as np

import geofunctions as zf


class GeoArray:
    def __str__(self):
        string = (
            'Zeph GeoArray Instance\n\n' +
            'Geotransform: {}\n'.format(self.geotransform) +
            'Projection:   {}\n'.format(self.proj4) +
            'Extent:       {}\n'.format(self.extent) +
            'Bands:        {}\n\n'.format(self.band_count) +
            'Array:\n{}'.format(self.array))
        return string

    def __init__(self, raster_filepath):
        self.in_memory = None
        self.filepath = raster_filepath
        self.input_ds = zf.raster_path_ds(raster_filepath, read_only=True)
        self.extent = zf.raster_ds_extent(self.input_ds)
        self.proj4 = zf.osr_proj4(zf.raster_ds_osr(self.input_ds))
        self.geotransform = zf.raster_ds_geo(self.input_ds)

        # DEADBEEF - add check for whether or not array can be held in memory
        if self.in_memory is None:
            pass
        self.band_count = self.input_ds.RasterCount
        if self.band_count is None:
            raise AttributeError(
                'The band_count of the input raster dataset is None')
        elif self.band_count == 1:
            array, input_nodata = zf.raster_to_array(
                raster_filepath, band=self.band_count, return_nodata=True)
            self.array = array
            self.nodata = input_nodata
            del array, input_nodata
        else:
            shape = (self.band_count,
                self.input_ds.RasterYSize, self.input_ds.RasterXSize)
            geo_array = np.empty(shape, dtype='float')
            for band in xrange(1, self.band_count):
                geo_array[band] = np.nan
                geo_array[band], input_nodata = zf.raster_to_array(
                    raster_filepath, band=band, return_nodata=True)
                geo_array[band][geo_array[band] == input_nodata] = np.nan
                del input_nodata
            self.array = geo_array
            self.nodata = np.nan

