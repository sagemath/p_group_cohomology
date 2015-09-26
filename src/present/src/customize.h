/*****************************************************************************
       Copyright (C) 2009 Simon A. King <simon.king@uni-jena.de>

  Distributed under the terms of the GNU General Public License (GPL),
  version 2 or later (at your choice)

    This code is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
    General Public License for more details.

  The full text of the GPL is available at:

                  http://www.gnu.org/licenses/
*****************************************************************************/
#include "meataxe.h"

void *copyrows(PTR dest, PTR src, size_t nor) { return memcpy((void *)dest, (void *)src, zsize(nor)); };

