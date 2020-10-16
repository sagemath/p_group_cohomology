#*****************************************************************************
#
#    Copyright (C) 2009-2020 Simon A. King <simon.king@uni-jena.de>
#
#    This file is part of p_group_cohomology.
#
#    p_group_cohomoloy is free software: you can redistribute it and/or modify
#    it under the terms of the GNU General Public License as published by
#    the Free Software Foundation, either version 2 of the License, or
#    (at your option) any later version.
#
#    p_group_cohomoloy is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#    GNU General Public License for more details.
#
#    You should have received a copy of the GNU General Public License
#    along with p_group_cohomoloy.  If not, see <http://www.gnu.org/licenses/>.
#*****************************************************************************

from setuptools import setup, find_packages
from setuptools.extension import Extension
from setuptools.command.build_ext import build_ext
from Cython.Build import cythonize
from sys import version_info
from sage.all import srange, singular
from sage.rings.integer import Integer

import os

# determine that we have a sufficiently new SageMath version to avoid
# all kinds of hastle with all the backwards incompatible changes in Sage
from sage.misc.banner import require_version
assert require_version(9,0,prerelease=True), "This spkg requires at least Sage 9.0"

CSAGE = []
CSAGE_PATH = []

# Sage >= 6.8
from sage.env import sage_include_directories

ext_mods = [
    Extension("pGroupCohomology.resolution",
              sources = [os.path.join("pGroupCohomology","resolution.pyx")],
              include_dirs = sage_include_directories(),
              libraries = ['mtx', 'modres']),

    Extension("pGroupCohomology.cochain",
              sources = [os.path.join("pGroupCohomology","cochain.pyx")],
              include_dirs = sage_include_directories(),
              libraries = ['mtx', 'modres']),

    Extension("pGroupCohomology.cohomology",
              sources = [os.path.join("pGroupCohomology","cohomology.pyx")],
              include_dirs = sage_include_directories(),
              libraries = ['mtx', 'modres']),

    Extension("pGroupCohomology.modular_cohomology",
              sources = [os.path.join("pGroupCohomology","modular_cohomology.pyx")],
              include_dirs = sage_include_directories(),
              libraries = ['mtx', 'modres']),

    Extension("pGroupCohomology.dickson",
              sources = [os.path.join("pGroupCohomology","dickson.pyx")],
              include_dirs = sage_include_directories())
    ]

if version_info.major <= 2:
    PY_MAJOR_VERSION = 2
elif version_info.major == 3 and version_info.minor >= 6:
    PY_MAJOR_VERSION = 3
else:
    raise RuntimeError("Unsupported version")

setup(
  name = "pGroupCohomology",
  version = "3.3.2",
  author = "Simon A. King, David J. Green",
  author_email = "simon.king@uni-jena.de, david.green@uni-jena.de",
  license = 'GPLv2+',
  classifiers = [
  'Development Status :: 4 - Beta',
  'Intended Audience :: Science/Research',
  'License :: OSI Approved :: GNU General Public License v2 or later (GPLv2+)',
  'Natural Language :: English',
  'Programming Language :: Cython',
  'Programming Language :: Other',
  'Topic :: Scientific/Engineering :: Mathematics'
  ],
  maintainer = "Simon A. King",
  maintainer_email = "simon.king@uni-jena.de",
  url = "https://users.fmi.uni-jena.de/cohomology/documentation/",
  description = "Modular Cohomology Rings of Finite Groups",
  packages = find_packages(),
  package_data = {'pGroupCohomology': ['*.pxd']},
  py_modules = ["pGroupCohomology.auxiliaries", "pGroupCohomology.barcode", "pGroupCohomology.factory", "pGroupCohomology.isomorphism_test"],
  ext_modules = cythonize(ext_mods, compiler_directives={'embedsignature': True,
                                                         'language_level': PY_MAJOR_VERSION}, build_dir=os.path.join("build","c_files-{}.{}".format(version_info.major, version_info.minor))),
  cmdclass = {'build_ext': build_ext}
)
