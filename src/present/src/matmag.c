/*
*  matmag.c : C program to convert matrix to MAGMA format
*  Author: David J Green
*  Created: 13 September 2000
*  Last altered: 13 September 2000
*/

#include "pgroup.h"
#include "pgroup_decls.h"
MTX_DEFINE_FILE_INFO

static MtxApplicationInfo_t AppInfo = {
    "matmag",

    "Convert matrix to MAGMA format.",

    "SYNTAX\n"
    "    matmag [-n <Magname>] <Mat> <Magfile>\n"
    "\n"
    "ARGUMENTS\n"
    "    <MTXfile> ....... File containing a MeatAxe matrix over a prime field\n"
    "    <Magfile> ....... File to write MAGMA matrix to\n"
    "\n"
    "OPTIONS\n"
    "    -n <Magname> .... MAGMA matrix will be called <Magname> (default A)\n"
    MTX_COMMON_OPTIONS_DESCRIPTION
    "\n"
};

static MtxApplication_t *App = NULL;

/***
 * control variables
 ****/

const char *MTXfile;
const char *Magfile;
const char *Magname;


/******************************************************************************/
int Init(int argc, const char *argv[])
{
  App = AppAlloc(&AppInfo,argc,argv);
  if (App == NULL)
	return 1;

  Magname = AppGetTextOption(App, "-n", "A");
  if (!MTXfile)
  { MTX_ERROR1("Empty string for option -n: %E", MTX_ERR_BADARG);
    return 1;
  }
  if (AppGetArguments(App, 2, 2) < 0)
	return 1;

  MTXfile = App->ArgV[0];
  Magfile = App->ArgV[1];
  return 0;
}

/******************************************************************************/
static long charLengthOfLong(long n)
{
  long m;
  if (n < 0) return 1 + charLengthOfLong(-n);
  if (n < 10) return 1;
  m = n / 10;
  return 1 + charLengthOfLong(m);
}

/******************************************************************************/
static long marksPerLine(long p, long noc)
{
  long m = (MAXLINE - 2) / (2 + charLengthOfLong(p-1));
  return minlong(m, noc);
}

/******************************************************************************/
static int writeMagmaMatrix(FILE *fp, Matrix_t *mat)
{
  char buffer[MAXLINE], tmp[MAXLINE];
  long mpl = marksPerLine(mat->Field, mat->Noc);
  PTR row;
  long i, j, thisrow = 0;
  buffer[0] = '\0';
  if (FfOrder != FfChar)
  { MTX_ERROR("writeMagmaMatrix: currently only prime fields catered for");
    return 1;
  }
  /* fprintf(fp, "%s := Matrix(GF(%ld), %ld, %ld, [\n", Magname, mat->Field,
    mat->Nor, mat->Noc); */
  fprintf(fp, "KMatSpace := KMatrixSpace(GF(%d), %d, %d);\n", mat->Field,
    mat->Nor, mat->Noc);
  fprintf(fp, "%s := KMatSpace ! [\n", Magname);
  for (i = 0; i < mat->Nor; i++)
  {
    row = MatGetPtr(mat, i);
    for (j = 0; j < mat->Noc; j++)
    {
      if (thisrow == mpl)
      {
        fprintf(fp, "%s\n", buffer);
        buffer[0] = '\0';
        thisrow = 0;
      }
      sprintf(tmp, " %d", FfToInt(FfExtract(row, j)));
      if (i < mat->Nor-1 || j < mat->Noc-1) strcat(tmp, ",");
      strcat(buffer, tmp);
      thisrow++;
    }
  }
  fprintf(fp, "%s\n", buffer);
  fprintf(fp, "];\n");
  return 0;
}

/******************************************************************************/
static int dumpMagmaMatrix(Matrix_t *mat)
{
  FILE *fp = SysFopen(Magfile, FM_CREATE);
  if (!fp) return 1;
  int r = writeMagmaMatrix(fp, mat);
  fclose(fp);
  return r;
}

/******************************************************************************/
static int convertMatrixToMagma()
{
  Matrix_t *mat = MatLoad(MTXfile);
  if (!mat) return 1;
  int r = dumpMagmaMatrix(mat);
  MatFree(mat);
  return r;
}

/******************************************************************************/
int main(int argc, const char *argv[])
{
  if (Init(argc, argv)) exit(1);
  if (convertMatrixToMagma()) exit(1);
  if (App != NULL)
      AppFree(App);
  exit(0);
}
