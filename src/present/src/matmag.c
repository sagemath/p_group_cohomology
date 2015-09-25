/*
*  matmag.c : C program to convert matrix to MAGMA format
*  Author: David J Green
*  Created: 13 September 2000
*  Last altered: 13 September 2000
*/

#include "pgroup.h"
#include "pgroup_decls.h"

static char *helptext[] = {
"SYNTAX",
"	matmag [-n <Magname>] <Mat> <Magfile>",
"",
"	<Mat> : File containing a MeatAxe matrix over a prime field",
"	<Magfile> : File to write MAGMA matrix to",
"	Option -n: MAGMA matrix called <Magname> (default A)",
"",
"DESCRIPTION",
"	Convert matrix to MAGMA format.",
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
  if (!control) AllocationError("newController");
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
void InterpretCommandLine(int argc, char *argv[], control_t *control)
{
  char invalid[MAXLINE];
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
  else OtherError(invalid);
  return;
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
static void writeMagmaMatrix(FILE *fp, matrix_t *mat, char *Magname)
{
  char buffer[MAXLINE], tmp[MAXLINE];
  long mpl = marksPerLine(mat->fl, mat->noc);
  PTR row;
  long i, j, thisrow = 0;
  buffer[0] = '\0';
  if (zfl != zchar)
    OtherError("writeMagmaMatrix: currently only prime fields catered for");
  /* fprintf(fp, "%s := Matrix(GF(%ld), %ld, %ld, [\n", Magname, mat->fl,
    mat->nor, mat->noc); */
  fprintf(fp, "KMatSpace := KMatrixSpace(GF(%ld), %ld, %ld);\n", mat->fl,
    mat->nor, mat->noc);
  fprintf(fp, "%s := KMatSpace ! [\n", Magname);
  for (i = 1; i <= mat->nor; i++)
  {
    row = ptrPlus(mat->d, i-1);
    for (j = 1; j <= mat->noc; j++)
    {
      if (thisrow == mpl)
      {
        fprintf(fp, "%s\n", buffer);
        buffer[0] = '\0';
        thisrow = 0;
      }
      sprintf(tmp, " %ld", zftoi(zextract(row, j)));
      if (i < mat->nor || j < mat->noc) strcat(tmp, ",");
      strcat(buffer, tmp);
      thisrow++;
    }
  }
  fprintf(fp, "%s\n", buffer);
  /* fprintf(fp, "]);\n"); */
  fprintf(fp, "];\n");
  return;
}

/******************************************************************************/
static void dumpMagmaMatrix(matrix_t *mat, char *Magfile, char *Magname)
{
  FILE *fp = SFOpen(Magfile, FM_CREATE);
  if (!fp) OtherError("dumpMagmaMatrix: opening file");
  writeMagmaMatrix(fp, mat, Magname);
  fclose(fp);
  return;
}

/******************************************************************************/
static void convertMatrixToMagma(char *Matname, char *Magfile, char *Magname)
{
  matrix_t *mat = matload(Matname);
  if (!mat) OtherError("convertMatrixToMagma: loading matrix");
  dumpMagmaMatrix(mat, Magfile, Magname);
  matfree(mat);
  return;
}

/******************************************************************************/
int main(int argc, char *argv[])
{
  control_t *control;
  mtxinit();
  control = newController();
  InterpretCommandLine(argc, argv, control);
  convertMatrixToMagma(control->Matname, control->Magfile, control->Magname);
  exit(0);
}
