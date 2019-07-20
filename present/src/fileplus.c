/*****************************************************************************
       Copyright (C) 2009 David J. Green <david.green@uni-jena.de>

    This file is part of p_group_cohomology.

    p_group_cohomoloy is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 2 of the License, or
    (at your option) any later version.

    p_group_cohomoloy is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with p_group_cohomoloy.  If not, see <http://www.gnu.org/licenses/>.
*****************************************************************************/
/* This is C code
*  fileplus.c : Allow read/write in Ringe's C MeatAxe
*  Author: David J Green
*  First version: 29 July 1996
*
*  Uses Ringe's C MeatAxe library functions.
*/

#include "fileplus.h"
#include "meataxe.h"

MTX_DEFINE_FILE_INFO

/**
 *  NULL on error
 *****/
FILE *os_fopenplus(char *name, int mode)
{
  FILE *fp;
  char *mode_str;
  switch (mode)
  {
    case FM_READ:
      mode_str = "r+b";
      break;
    case FM_CREATE:
      mode_str = "w+b";
      break;
    case FM_APPEND:
      mode_str = "a+b";
      break;
    default:
      MTX_ERROR1("Illegal mode in os_fopenplus: %E", MTX_ERR_FILEFMT);
      mode_str = "";
      return NULL;
  }
  fp = fopen(name,mode_str);
  if (!fp) MTX_ERROR1("Cannot open file %s", name);
  return fp;
}


/**
 * 1 on error
 ********/
int alterhdrplus(FILE *fp, long nor)
{
  long header[3];
  if (SysFseek(fp,(long)0))
  { MTX_ERROR1("%E", MTX_ERR_FILEFMT);
    return 1;
  }
  if (SysReadLong(fp,header,3) != 3)
  {
    fclose(fp);
    MTX_ERROR1("%E", MTX_ERR_FILEFMT);
    return 1;
  }
  header[1] = nor;
  if (SysFseek(fp,(long)0))
  {
    fclose(fp);
    MTX_ERROR1("%E", MTX_ERR_FILEFMT);
    return 1;
  }

  if (SysWriteLong(fp,header,3) != 3)
  {
    fclose(fp);
    MTX_ERROR1("%E", MTX_ERR_FILEFMT);
    return 1;
  }
  if (SysFseek(fp,(long)12))
  {
    fclose(fp);
    MTX_ERROR1("%E", MTX_ERR_FILEFMT);
    return 1;
  }
  return 0;
}

/**
 * NULL on error
 ******/
FILE *writehdrplus(char *name, long fl, long nor, long noc)
{
  FILE *fp;
  long header[3];
  header[0] = (long)fl;
  header[1] = (long)nor;
  header[2] = (long)noc;
  fp = os_fopenplus(name, FM_CREATE);
  if (!fp)
  {
    MTX_ERROR1("%E", MTX_ERR_FILEFMT);
    return NULL;
  }
  if (SysWriteLong(fp,header,3) != 3)
  {
    fclose(fp);
    MTX_ERROR1("%E", MTX_ERR_FILEFMT);
    return NULL;
  }
  return fp;
}

/**
 * NULL on error
 ****/
FILE *readhdrplus(char *name, long *fl, long *nor, long *noc)
/* Opens existing file for read/write */
/* Assigns to fl, nor, noc, unless NULL */
{
  FILE *fp;
  long header[3];
  fp = os_fopenplus(name, FM_READ);
  if (!fp)
  {
    MTX_ERROR1("%E", MTX_ERR_FILEFMT);
    return NULL;
  }
  if (SysReadLong(fp,header,3) != 3)
  {
    fclose(fp);
    MTX_ERROR1("%E", MTX_ERR_FILEFMT);
    return NULL;
  }
  if (fl != NULL)
    *fl = header[0];
  if (nor != NULL)
    *nor = header[1];
  if (noc != NULL)
    *noc = header[2];
  if (SysFseek(fp,(long)12))
  {
    fclose(fp);
    MTX_ERROR1("%E", MTX_ERR_FILEFMT);
    return NULL;
  }
  return fp;
}

/**
 * -1 on error
 ****/
long numberOfRowsStored(char *name)
{
  FILE *fp;
  int fl, nor, noc;
  fp = FfReadHeader(name, &fl, &nor, &noc);
  if (!fp)
  {
    MTX_ERROR2("opening file %s: %E", name, MTX_ERR_FILEFMT);
    return -1;
  }
  fclose(fp);
  return nor;
}
