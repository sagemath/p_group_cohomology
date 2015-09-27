/*
*  matmag.c : C program to convert matrix to MAGMA format
*  Author: David J Green
*  Created: 13 September 2000
*  Last altered: 13 September 2000
*/

#include "pgroup.h"
#include "pgroup_decls.h"
MTX_DEFINE_FILE_INFO

static char *helptext[] = {
"SYNTAX",
"   matmag [-n <Magname>] <Mat> <Magfile>",
"",
"   <Mat> : File containing a MeatAxe matrix over a prime field",
"   <Magfile> : File to write MAGMA matrix to",
"   Option -n: MAGMA matrix called <Magname> (default A)",
"",
"DESCRIPTION",
"   Convert matrix to MAGMA format.",
NULL};

static proginfo_t pinfo =
  { "matmag", "Convert matrix to MAGMA format.",
    "$Revision: 13_September_2000", helptext };

/******************************************************************************/
struct controlVariables
{
  char Matname[MAXLINE];
  char Magfile[MAXLINE];
  char Magname[MAXLINE];
};

typedef struct controlVariables control_t;

/******************************************************************************/
control_t *newController(void)
{
  control_t *control = (control_t *) malloc(sizeof(control_t));
  if (!control)
  { MTX_ERROR1("%E", MTX_ERR_NOMEM);
    return NULL;
  }

  sprintf(control->Magname, "A");
  return control;
}

/******************************************************************************/
void freeController(control_t *control)
{
  free(control);
  return;
}

/******************************************************************************/
int InterpretCommandLine(int argc, char *argv[], control_t *control)
{
  initargs(argc,argv,&pinfo);
  sprintf(invalid,
    "Invalid command line. Issue \"%s -help\" for more details", pinfo.name);
  while (zgetopt("n:") != OPT_END)
  {
    sprintf(control->Magname, "%s", opt_text);
  }
  if (opt_ind == argc - 2)
  {
    char *this;
    this = argv[opt_ind++];
    strcpy(control->Matname, this);
    this = argv[opt_ind++];
    strcpy(control->Magfile, this);
  }
  else
  { MTX_ERROR1("%E", MTX_ERR_BADARG);
    return 1;
  }
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
static int writeMagmaMatrix(FILE *fp, Matrix_t *mat, char *Magname)
{
  char buffer[MAXLINE], tmp[MAXLINE];
  long mpl = marksPerLine(mat->fl, mat->noc);
  PTR row;
  long i, j, thisrow = 0;
  buffer[0] = '\0';
  if (FfOrder != FfChar)
  { MTX_ERROR("writeMagmaMatrix: currently only prime fields catered for");
    return 1;
  }
  /* fprintf(fp, "%s := Matrix(GF(%ld), %ld, %ld, [\n", Magname, mat->fl,
    mat->nor, mat->noc); */
  fprintf(fp, "KMatSpace := KMatrixSpace(GF(%ld), %ld, %ld);\n", mat->fl,
    mat->nor, mat->noc);
  fprintf(fp, "%s := KMatSpace ! [\n", Magname);
  for (i = 0; i < mat->nor; i++)
  {
    row = FfGetPtr(mat->d, i);
    for (j = 0; j < mat->noc; j++)
    {
      if (thisrow == mpl)
      {
        fprintf(fp, "%s\n", buffer);
        buffer[0] = '\0';
        thisrow = 0;
      }
      sprintf(tmp, " %ld", FfToInt(FfExtract(row, j)));
      if (i < mat->nor-1 || j < mat->noc-1) strcat(tmp, ",");
      strcat(buffer, tmp);
      thisrow++;
    }
  }
  fprintf(fp, "%s\n", buffer);
  /* fprintf(fp, "]);\n"); */
  fprintf(fp, "];\n");
  return 0;
}

/******************************************************************************/
static int dumpMagmaMatrix(Matrix_t *mat, char *Magfile, char *Magname)
{
  FILE *fp = SysFopen(Magfile, FM_CREATE);
  if (!fp) return 1;
  int r = writeMagmaMatrix(fp, mat, Magname);
  fclose(fp);
  return r;
}

/******************************************************************************/
static int convertMatrixToMagma(char *Matname, char *Magfile, char *Magname)
{
  Matrix_t *mat = MatLoad(Matname);
  if (!mat) return 1;
  int r = dumpMagmaMatrix(mat, Magfile, Magname);
  MatFree(mat);
  return r;
}

/******************************************************************************/
int main(int argc, char *argv[])
{
  control_t *control;
  MtxInitLibrary();
  control = newController();
  if (InterpretCommandLine(argc, argv, control)) exit(1);
  if (convertMatrixToMagma(control->Matname, control->Magfile, control->Magname)) exit(1);
  exit(0);
}
