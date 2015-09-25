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
/* module_decls.h : header file containing declarations in module.c */

#if !defined(__MODULE_DECLS_INCLUDED)	/* Include only once */
#define __MODULE_DECLS_INCLUDED

module_t *newModuleRecord(void);
module_t *namedModuleRecord(char *MStem);
module_t *loadModuleAction(group_t *group, module_t *module);
void freeModule(module_t *module);
void saveModule(group_t *group, module_t *module);
module_t *allocateModule(group_t *group, long dimM);
void moduleMinusOne(group_t *group, module_t *src, module_t *dest);
void dualModule(group_t *group, module_t *src, module_t *dest);

#endif
