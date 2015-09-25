#*****************************************************************************
#
#    Copyright (C) 2009/10 Simon A. King <simon.king@nuigalway.ie>
#    Copyright (C) 2013 Simon A. King <simon.king@uni-jena.de>
#
#  Distributed under the terms of the GNU General Public License (GPL),
#  version 2 or later (at your choice)
#
#    This code is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
#    General Public License for more details.
#
#  The full text of the GPL is available at:
#
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from distutils.core import setup
from distutils.extension import Extension
from Cython.Distutils import build_ext
from sage.all import srange, singular
from sage.rings.integer import Integer

import shutil
import os
import subprocess

try:
    from sage.env import SAGE_SRC, SAGE_LOCAL, SAGE_SHARE, SAGE_EXTCODE
except ImportError:
    try:
        from sage.misc.misc import SAGE_SRC, SAGE_LOCAL, SAGE_SHARE, SAGE_EXTCODE
    except ImportError:
        print "##################################"
        print "##  Sage version predates 6.0   ##"
        print "##################################"
        from sage.misc.misc import SAGE_DATA as SAGE_SHARE
        from sage.misc.misc import SAGE_ROOT
        SAGE_SRC = os.path.join(SAGE_ROOT, 'devel','sage')
        SAGE_LOCAL = os.path.join(SAGE_ROOT,'local')
        SAGE_EXTCODE = os.path.join(SAGE_SHARE,"sage","ext")

SRC_EXT = os.path.join(SAGE_SRC,"sage","ext")
# determine whether we have a sufficiently new SageMath version to avoid
# linking against csage
try:
    from sage.misc.banner import require_version
    if require_version(6,7):
        CSAGE = []
        CSAGE_PATH = []
    else:
        CSAGE = ["csage"]
        CSAGE_PATH = [os.path.join(SAGE_LOCAL,"include","csage")]
except ImportError:
    CSAGE = ["csage"]
    CSAGE_PATH = [os.path.join(SAGE_LOCAL,"include","csage")]

try:
    # Sage >= 6.8
    from sage.env import sage_include_directories
except ImportError:
    # Sage < 6.8
    def sage_include_directories():
        return [
            CSAGE_PATH,
            os.path.join(SAGE_SRC, "c_lib", "include"),
            SAGE_EXTCODE, SRC_EXT]

# Copy our singular libraries to the right place

try:
    SingularLib=os.environ['SINGULARPATH']
except KeyError:
    SingularLib=singular.eval('system("SingularLib")').split(':')[0]
shutil.copy(os.path.join('pGroupCohomology','dickson.lib'),SingularLib)
shutil.copy(os.path.join('pGroupCohomology','filterregular.lib'),SingularLib)

PrimePowers = [n for n in srange(2,256) if Integer(n).is_prime_power()]
os.chdir('lib')
for n in PrimePowers:
    subprocess.call([os.path.join('..','bin','maketab'),'%d'%n])
os.chdir('..')

mtx_tables = [os.path.join('lib',s) for s in os.listdir('lib') if s.endswith('zzz')]

setup(
  name = "pGroupCohomology",
  version = "2.1.5",
  author = "Simon A. King, David J. Green",
  author_email = "simon.king@uni-jena.de, david.green@uni-jena.ie",
  maintainer = "Simon A. King", 
  maintainer_email = "simon.king@uni-jena.de",
  url = "http://users.minet.uni-jena.de/cohomology/documentation/",
  description = "Modular Cohomology Rings of Finite Groups",
  packages=["pGroupCohomology"],
  py_modules = ["pGroupCohomology.barcode","pGroupCohomology.factory"],
  data_files=[("pGroupCohomology",
              [os.path.join("pGroupCohomology","GroupNames.sobj"),
               os.path.join("pGroupCohomology","GapMaxels"),
               os.path.join("pGroupCohomology","GapMB"),
               os.path.join("pGroupCohomology","GapSgs")]),
              ("pGroupCohomology", [os.path.join('db',X) for X in os.listdir('db')]+[os.path.join("db","LICENCE")]),
              (os.path.join("pGroupCohomology","mtx_tables"), mtx_tables)],
  ext_modules=[ 
    Extension("pGroupCohomology.resolution",
              sources = [os.path.join("pGroupCohomology","resolution.pyx"),
                         os.path.join("pGroupCohomology","c_sources","aufloesung.c"),
                         os.path.join("pGroupCohomology","c_sources","aufnahme.c"),
                         os.path.join("pGroupCohomology","c_sources","djgerr.c"),
                         os.path.join("pGroupCohomology","c_sources","fileplus.c"),
                         os.path.join("pGroupCohomology","c_sources","nBuchberger.c"),
                         os.path.join("pGroupCohomology","c_sources","pgroup.c"),
                         os.path.join("pGroupCohomology","c_sources","pincl.c"),
                         os.path.join("pGroupCohomology","c_sources","slice.c"),
                         os.path.join("pGroupCohomology","c_sources","urbild.c"),
                         os.path.join("pGroupCohomology","c_sources","uvr.c")],
              libraries = ["mtx"] + CSAGE,
              extra_compile_args=["-O3"],
              #extra_link_args=["-g"],
              include_dirs = sage_include_directories() + [
                              os.path.join("mtx2.2.4","src"),
                              os.path.join("pGroupCohomology","c_sources"),
                              "pGroupCohomology"]
              ),
    Extension("pGroupCohomology.cohomology",
              sources = [os.path.join("pGroupCohomology","cohomology.pyx"),
                         os.path.join("pGroupCohomology","c_sources","aufloesung.c"),
                         os.path.join("pGroupCohomology","c_sources","aufnahme.c"),
                         os.path.join("pGroupCohomology","c_sources","djgerr.c"),
                         os.path.join("pGroupCohomology","c_sources","fileplus.c"),
                         os.path.join("pGroupCohomology","c_sources","nBuchberger.c"),
                         os.path.join("pGroupCohomology","c_sources","pgroup.c"),
                         os.path.join("pGroupCohomology","c_sources","pincl.c"),
                         os.path.join("pGroupCohomology","c_sources","slice.c"),
                         os.path.join("pGroupCohomology","c_sources","urbild.c"),
                         os.path.join("pGroupCohomology","c_sources","uvr.c")],
              libraries = ["mtx"] + CSAGE,
              extra_compile_args=["-O3"],
              include_dirs = sage_include_directories() + [
                              os.path.join("mtx2.2.4","src"),
                              os.path.join("pGroupCohomology","c_sources"),
                              "pGroupCohomology"]
              ),
    Extension("pGroupCohomology.modular_cohomology",
              sources = [os.path.join("pGroupCohomology","modular_cohomology.pyx"),
                         os.path.join("pGroupCohomology","c_sources","aufloesung.c"),
                         os.path.join("pGroupCohomology","c_sources","aufnahme.c"),
                         os.path.join("pGroupCohomology","c_sources","djgerr.c"),
                         os.path.join("pGroupCohomology","c_sources","fileplus.c"),
                         os.path.join("pGroupCohomology","c_sources","nBuchberger.c"),
                         os.path.join("pGroupCohomology","c_sources","pgroup.c"),
                         os.path.join("pGroupCohomology","c_sources","pincl.c"),
                         os.path.join("pGroupCohomology","c_sources","slice.c"),
                         os.path.join("pGroupCohomology","c_sources","urbild.c"),
                         os.path.join("pGroupCohomology","c_sources","uvr.c")],
              libraries = ["mtx"] + CSAGE,
              extra_compile_args=["-O3"],
              include_dirs = sage_include_directories() + [
                              os.path.join("mtx2.2.4","src"),
                              os.path.join("pGroupCohomology","c_sources"),
                              "pGroupCohomology"]
              ),
    Extension("pGroupCohomology.cochain",
              sources = [os.path.join("pGroupCohomology","cochain.pyx"),
                         os.path.join("pGroupCohomology","c_sources","aufloesung.c"),
                         os.path.join("pGroupCohomology","c_sources","aufnahme.c"),
                         os.path.join("pGroupCohomology","c_sources","djgerr.c"),
                         os.path.join("pGroupCohomology","c_sources","fileplus.c"),
                         os.path.join("pGroupCohomology","c_sources","nBuchberger.c"),
                         os.path.join("pGroupCohomology","c_sources","pgroup.c"),
                         os.path.join("pGroupCohomology","c_sources","pincl.c"),
                         os.path.join("pGroupCohomology","c_sources","slice.c"),
                         os.path.join("pGroupCohomology","c_sources","urbild.c"),
                         os.path.join("pGroupCohomology","c_sources","uvr.c")],
              libraries = ["mtx"]+CSAGE,
              extra_compile_args=["-O3"],
              include_dirs = sage_include_directories() + [
                              os.path.join("mtx2.2.4","src"),
                              os.path.join("pGroupCohomology","c_sources"),
                              "pGroupCohomology"]
              ),
    Extension("pGroupCohomology.mtx",
              sources = [os.path.join("pGroupCohomology","mtx.pyx")],
              libraries = ["mtx"] + CSAGE,
              extra_compile_args=["-O3"],
              #extra_link_args=["-g"],
              include_dirs = sage_include_directories() + [
                              os.path.join("mtx2.2.4","src"),
                              os.path.join("pGroupCohomology","c_sources"),
                              "pGroupCohomology"]
              ),
    Extension("pGroupCohomology.dickson", sources = [os.path.join("pGroupCohomology","dickson.pyx")])
    ],
  cmdclass = {'build_ext': build_ext}
)

#######################
## Take care of the data base
tar_base = os.path.join(SAGE_LOCAL,'pGroupCohomology')
# create data base, if necessary
data_base = os.path.join(SAGE_SHARE,'pGroupCohomology')
try:
    os.mkdir(data_base)
except OSError, msg:
    if not ("File exists" in msg):
        raise OSError, msg

# transfer/extract data
os.rename(os.path.join(tar_base,'LICENCE'), os.path.join(data_base,'LICENCE'))
L = [os.path.join(tar_base,X) for X in os.listdir(tar_base) if X.endswith('.tar.gz')]
import tarfile, sys
print 'Extracting data base...'
sys.stdout.flush()
for f in L:
    T = tarfile.open(f)
    T.extractall(path=data_base)
    T.close()
    os.unlink(f)
