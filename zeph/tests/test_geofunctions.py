# Run with nose from top-level dir, ./zeph
from __future__ import absolute_import
import os
import sys
import unittest

import fiona
from zeph import geofunctions as zf


class GeojsonTestCase(unittest.TestCase):
    def setUp(self):
        self.geojson_filepath = os.path.join(
            os.getcwd(), 'zeph', 'tests', 'test_files', 'test.geojson')
        self.extent = zf.extent((-115.5, 35.264, -115., 37.))
        self.fiona_polygon = fiona.open(self.geojson_filepath, 'r')
        self.test_string_filepath = os.path.join(
            os.getcwd(), 'zeph', 'tests', 'test_files', 'test_geojson.txt')

    def tearDown(self):
        self.geojson_filepath = None
        self.extent = None
        self.fiona_polygon.close()
        self.fiona_polygon = None
        self.test_string_filepath = None

    def test_subset_geojson(self):
        self.assertEqual(
            zf.subset_geojson(self.geojson_filepath, self.extent),
            open(self.test_string_filepath, 'r').readlines()[0])