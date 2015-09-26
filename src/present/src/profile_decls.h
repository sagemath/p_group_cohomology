/*****************************************************************************
       Copyright (C) 2009 David J. Green <david.green@uni-jena.de>

  Distributed under the terms of the GNU General Public License (GPL),
  version 2 or later (at your choice)

    This code is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
    General Public License for more details.

  The full text of the GPL is available at:

                  http://www.gnu.org/licenses/
*****************************************************************************/
/* profile_decls.h : This is a C header file */
/* First version: 08 September 1997 by David J Green */

#if !defined(__PROFILE_DECLS_INCLUDED)	/* Include only once */
#define __PROFILE_DECLS_INCLUDED

void initializeProfiling(char *name, int profs);
void continueProfiling(char *name, int profs);
void profile(int n);
void stopProfiling(void);
void recordProfiles(void);

#endif
