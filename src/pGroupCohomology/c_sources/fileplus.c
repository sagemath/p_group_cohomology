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
/* This is C code
*  fileplus.c : Allow read/write in Ringe's C MeatAxe
*  Author: David J Green
*  First version: 29 July 1996
*
*  Uses Ringe's C MeatAxe library functions.
*/

#include "fileplus.h"

FILE *os_fopenplus(char *name, int mode)
{
  char *canonical_name = os_mkfilename(name);
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
      OtherError("Illegal mode in os_fopenplus");
      mode_str = "";
      break;
  }
  fp = fopen(canonical_name,mode_str);
  return fp;
}

int alterhdrplus(FILE *fp, long nor)
{
  long header[3];
  SFSeek(fp,(long)0);
  if (zreadlong(fp,header,3) != 3)
  {
    fclose(fp);
    mtxerror("alterhdrplus");
  }
  /* if (header[1] > nor)
  *  {
    *  fclose(fp);
    *  OtherError("Can't (yet) shorten files");
  *  }
  */
  header[1] = nor;
  SFSeek(fp,(long)0);
  if (zwritelong(fp,header,3) != 3)
  {
    fclose(fp);
    OtherError("Altering header");
  }
  SFSeek(fp,(long)12);
  return 0;
}

FILE *writehdrplus(char *name, long fl, long nor, long noc)
{
  FILE *fp;
  long header[3];
  header[0] = (long)fl;
  header[1] = (long)nor;
  header[2] = (long)noc;
  fp = os_fopenplus(name, FM_CREATE);
  if (!fp) MTXFAIL(ERR_FILEOPEN,NULL);
  if (zwritelong(fp,header,3) != 3)
  {
    fclose(fp);
    MTXFAIL(ERR_FILEWRITE,NULL);
  }
  return fp;
}

FILE *readhdrplus(char *name, long *fl, long *nor, long *noc)
/* Opens existing file for read/write */
/* Assigns to fl, nor, noc, unless NULL */
{
  FILE *fp;
  long header[3];
  fp = os_fopenplus(name, FM_READ);
  if (!fp) MTXFAIL(ERR_FILEOPEN,NULL);
  if (zreadlong(fp,header,3) != 3)
  {
    fclose(fp);
    MTXFAIL(ERR_FILEREAD,NULL);
  }
  if (fl != NULL)
    *fl = header[0];
  if (nor != NULL)
    *nor = header[1];
  if (noc != NULL)
    *noc = header[2];
  SFSeek(fp,(long)12);
  return fp;
}

void PrintMatrixFile(char *matname)
{
  char buffer[200];
  strcpy(buffer,"zpr ");
  strcat(buffer,matname);
  strcat(buffer," >> yyyy");
  system(buffer);
}

long numberOfRowsStored(char *name)
{
  FILE *fp;
  long fl, nor, noc;
  fp = zreadhdr(name, &fl, &nor, &noc);
  if (!fp)
  {
    char buffer[MAXLINE];
    sprintf(buffer, "numberOfRowsStored: opening file %s", name);
    OtherError(buffer);
  }
  fclose(fp);
  return nor;
}
