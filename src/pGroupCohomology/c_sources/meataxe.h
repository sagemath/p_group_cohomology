/* ========================== C MeatAxe =============================
   meataxe.h - Declarations for MeatAxe library functions.

   (C) Copyright 1994 Michael Ringe, Lehrstuhl D fuer Mathematik,
   RWTH Aachen, Germany  <mringe@tiffy.math.rwth-aachen.de>
   This program is free software; see the file COPYING for details.
   ================================================================== */

#if !defined(__MEATAXE_INCLUDED)	/* Include only once */
#define __MEATAXE_INCLUDED

#include <sys/types.h>
#include <stdio.h>
#include <string.h>
#define _GNU_SOURCE
#include <stdlib.h>

/* ------------------------------------------------------------------
   System dependencies.
   ------------------------------------------------------------------ */

#if defined(OS_SUNOS_41)

#   define PROTO_CLOCK
#   define PROTO_GETRUSAGE
#   define PROTO_MEMSET
#   define PROTO_PERROR
#   define PROTO_SETITIMER
#   define PROTO_STDIO

#elif defined(OS_ULTRIX)

#   define PROTO_GETRUSAGE
#   define PROTO_SETITIMER

#elif defined(OS_HPUX)

#   define NO_GETRUSAGE

#elif defined(OS_IBMVM)

#    define FMODES  "a, recfm=f, lrecl=80", "r, recfm=f, lrecl=80",\
          "w, recfm=f, lrecl=80", "ab, recfm=f, lrecl=256",\
          "rb, recfm=f, lrecl=256", "wb, recfm=f, lrecl=256"
  
#endif




/* ------------------------------------------------------------------
   System-dependent Functions (os.c)
   ------------------------------------------------------------------ */

void SInit(void);
long STimeUsed(void);
void STimeLimit(long nsec);
long SClock(void);

/* Memory */
#define ALLOC(type) ((type *) Smalloc(sizeof(type)))
#define NALLOC(type,n) ((type *) Smalloc((size_t)(n) * sizeof(type)))
#define NREALLOC(x,type,n)\
	((type *) Srealloc(x,(size_t)(n) * sizeof(type)))
void *Smalloc(size_t nbytes);
void *Srealloc(void *buf, size_t nbytes);

/* Files */
#define FM_READ 1
#define FM_CREATE 2
#define FM_APPEND 3
#define FM_TEXT 0x10
#define FM_LIB 0x20
FILE *SFOpen(char *name, int mode);
int SFSeek(FILE *f,long pos);
char *os_mkfilename(char *name);

/* Fix missing ptototypes */

#if defined(PROTO_STDIO)
#   define PROTO_FCLOSE
#   define PROTO_FFLUSH
#   define PROTO_FPRINTF
#   define PROTO_FREAD
#   define PROTO_FSCANF
#   define PROTO_FWRITE
#   define PROTO_PRINTF
#   define PROTO_SCANF
#   define PROTO_SSCANF
#endif


#if defined(PROTO_FCLOSE)
extern int fclose(FILE *);
#endif

#if defined(PROTO_FFLUSH)
extern int fflush(FILE *stream);
#endif

#if defined(PROTO_FPRINTF)
extern int fprintf(FILE *f, const char *format, ... );
#endif

#if defined(PROTO_FREAD)
extern size_t fread(void *buf, size_t size, size_t n, FILE *f); 
#endif

#if defined(PROTO_FSCANF)
extern int fscanf(FILE *f, const char *format, ... );
#endif

#if defined(PROTO_MEMSET)
extern void *memset(void *buf, int c, size_t n);
#endif

#if defined(PROTO_PERROR)
extern void perror(const char *msg);
#endif

#if defined(PROTO_PRINTF)
extern int printf(const char *format, ... );
#endif

#if defined(PROTO_SCANF)
extern int scanf(const char *format, ... );	
#endif

#if defined(PROTO_SPRINTF)
extern int sprintf(char *s, const char *format, ... );
#endif

#if defined(PROTO_SSCANF)
extern int sscanf(const char *s, const char *format, ...);
#endif

#if defined(PROTO_FWRITE)
extern size_t fwrite(const void *buf,size_t size,size_t n,FILE *f);
#endif



/* ------------------------------------------------------------------
   MeatAxe data types
   ------------------------------------------------------------------ */

#define T_MATRIX 1
#define T_PERM 2
#define T_POLY 3
#define T_SET 4
#define T_BITS 5
#define T_INTEGER 6
#define T_STRINGS 7
#define T_IMAT 8
#define T_SEQUENCE 20
#define T_FPOLY 21


/* ------------------------------------------------------------------
   Some typedef's
   ------------------------------------------------------------------ */

typedef unsigned long Ulong;
typedef unsigned short Ushort;
typedef unsigned char Uchar;


/* ------------------------------------------------------------------
   Return codes
   ------------------------------------------------------------------ */

#define	EXIT_OK		0	/* Exit code: normal end */
#define EXIT_ERR	1	/*            error */


/* MeatAxe error codes */

#define ERR_NULL	0	/* */
#define ERR_NOMEM	1	/* Not enough memory */
#define ERR_GAMEOVER	2	/* Time limit exceeded */
#define ERR_DIV0	8	/* Division by 0 or singular Matrix */

#define ERR_FILE	20	/* File errors */
#define ERR_FILEOPEN	21	/* Could not open */
#define ERR_FILEREAD	22	/* Read error */
#define ERR_FILEWRITE	23	/* Write error */
#define ERR_FILEFMT	24	/* Bad format */
#define ERR_NFILES	25	/* Too many files */
#define ERR_EOF		26	/* Unexpected EOF */

#define ERR_ARGS	30	/* Arguments */
#define ERR_BADARG	31	/* Bad argument */
#define ERR_BADTYPE	32	/* Bad type */
#define ERR_RANGE	33	/* Out of range */
#define ERR_NOTECH	34	/* Matrix not in chelon form */
#define ERR_NOTSQUARE	35	/* Matrix not square */
#define ERR_INCOMPAT	36	/* Arguments are incompatible */

#define ERR_USAGE	40
#define ERR_BADUSAGE	41	/* Bad command line */
#define ERR_OPTION	42	/* Bad usage of option */
#define ERR_NARGS	43	/* Bad number of arguments */

#define ERR_NOTMATRIX	51	/* Not a matrix */
#define ERR_NOTPOLY	52	/* Not a polynomial */
#define ERR_NOTPERM	53	/* Not a permutation */

#define ERR_UNKNOWN	61	/* Unkown symbol */


/* ------------------------------------------------------------------
   Kernel specific part
   ------------------------------------------------------------------ */

#if !defined(ZZZ)		/* Assume default if undefined */
#define ZZZ zzz
#endif

/* ZZZ kernel for small fields (default)
   ------------------------------------- */
#if ZZZ==zzz

typedef unsigned char FEL;
typedef FEL *PTR;
#define F_ZERO ((FEL)0)
#define F_ONE ((FEL)1)
#define ZZZVERSION 6
extern FEL tmult[256][256];
extern FEL tadd[256][256];
extern FEL taddinv[256], tmultinv[256];
#define zadd(a,b) ((FEL)tadd[(unsigned char)a][(unsigned char)b])
#define zmul(a,b) ((FEL)tmult[(unsigned char)a][(unsigned char)b])
#define zneg(a) (taddinv[(unsigned char)a])
#define zinv(a) (tmultinv[(unsigned char)a])


/* BIGZZZ kernel for field orders up to 2^{16}
   ------------------------------------------- */ 

#elif ZZZ==bigzzz

typedef unsigned short FEL;
typedef unsigned short *PTR;
#define F_ZERO ((FEL)0xFFFF)
#define F_ONE ((FEL)0)
#define ZZZVERSION 0x101

#endif



/* ------------------------------------------------------------------
   Common definition for all kernels
   ------------------------------------------------------------------ */

extern long zfl, zchar;		/* Field order and characteristic */
extern FEL zgen;		/* Generator */
extern long znoc;		/* Number of columns for row ops */
extern size_t zrowsize;		/* Row size in memory */
extern size_t zrowsize_io;	/* Row size in files */
extern char zzzversion[];
extern char zzz_cc[];

typedef struct
{
  long i;      /* position of the pivot */
  long m;      /* value of the pivot */
} piv_t;


/* Simon King (2008-12) define some more basic 
   functions by macros.
   ------------------------------------------------- */

#if !defined(zadd)
FEL zadd(FEL a,FEL b);
#endif
#if !defined(zneg)
FEL zneg(FEL a);
#endif
#if !defined(zmul)
FEL zmul(FEL a,FEL b);
#endif
#if !defined(zinv)
FEL zinv(FEL a);
#endif

#if !defined(zembed)
FEL zembed(FEL a, long subfield);	/* Embed from subfield */
#endif
#if !defined(zrestrict)
FEL zrestrict(FEL a, long subfield);	/* Restrict to subfield */
#endif

// protect zfl
#if !defined(zfl)
#define zfl zfl
#endif

#if !defined(zitof)
#define zitof(l) ( {register long f; f = (l) % zfl; (f < 0) ? (FEL)(f+zfl) : (FEL) f;} )
#endif

#if !defined(zftoi)
#define zftoi(f) ((long) f)
#endif


/* Function prototypes. Some of these may be defined
   as macros in the kernel specific part.
   ------------------------------------------------- */

int zsetfield(long field);
int zsetlen(long ncols);		/* Set row size */

// zextract, zinsert are defined below as a macro

long zfindpiv(PTR row, FEL *mark);
piv_t _zfindpiv_(PTR row);
PTR zextractcol(PTR mat, long nor, long col, PTR result);
PTR zaddrow(PTR dest, PTR src);
PTR zsubrow(PTR dest, PTR src);
PTR zmulrow(PTR row, FEL mark);
PTR zaddmulrow(PTR dest, PTR src, FEL f);
PTR zmaprow(PTR row, PTR matrix, long nor, PTR result);
PTR zpermrow(PTR row, long *perm, PTR result);


/* ------------------------------------------------------------------
   Other low-level functions (zzz2.c)
   Simon King (2008-12): define some of them as macros
   ------------------------------------------------------------------ */

#define zsub(a,b) zadd((a),zneg(b))
#define zdiv(a,b) zmul((a),zinv(b))

inline void zmoverow(PTR dest, PTR src);
inline void zcpyrow(PTR dest, PTR src, long sz);
void zswaprow(PTR dest, PTR src);
int zcmprow(PTR dest, PTR src);
inline size_t zsize(long nrows);
PTR zalloc(long NROWS);
inline void zfree(PTR p);
extern size_t LPR; // long per row
extern size_t MPB; // marks per byte
extern unsigned char tffirst[256][2],
	textract[8][256],
	tnull[8][256],
	tinsert[8][256];

// instead of inline functions, define macros!
// first, a trick in order to protect MPB etc from being evaluated too early
#if !defined(MPB)
#define MPB MPB
#endif
#if !defined(textract)
#define textract textract
#endif

// inline FEL zextract(PTR row, long col);
#if !defined(zextract)
#define zextract(row, col) ({ register long COL = (col)-1; (textract[COL % MPB][*((unsigned char *)(row) + (COL / MPB))]); })
#endif

// inline void zinsert(PTR row, long col, FEL mark);
// NOTE: I removed CHECKFEL.
#if !defined(tnull)
#define tnull tnull
#endif
#if !defined(tinsert)
#define tinsert tinsert
#endif
#if !defined(zinsert)
#define zinsert(row, col, mark) {register long COL = (col)-1; register unsigned char *LOC = (unsigned char *)(row) + (COL / MPB); register long IDX = COL % MPB; *LOC = tnull[IDX][*LOC] + tinsert[IDX][mark];} 
#endif

// inline void zadvance(PTR *ptr, long nrows);
// inline void zsteprow(PTR *ptr);
// inline void zbackrow(PTR *ptr);
// inline PTR ptrPlus(PTR base, long offset);
inline void zinsert_step(PTR *pos, int *idx, FEL mark);
inline FEL zextract_step(PTR *pos, int *idx);

// protecting LPR 
#if !defined(LPR)
#define LPR LPR
#endif

#if !defined(zadvance)
#define zadvance(ptr,nrows) (*(long **)(ptr) += ((nrows) * (LPR)))
#endif

#if !defined(zsteprow)
#define zsteprow(ptr) ( *(long **)(ptr) += (LPR) )
#endif

#if !defined(zbackrow)
#define zbackrow(ptr) ( *(long **)(ptr) -= (LPR) )
#endif

#if !defined(ptrPlus)
#define ptrPlus(ptr, nrows) ((PTR)((*(long **)&(ptr)) + ((nrows) * (LPR))))
#endif


/**************************************************************************/
int mtxinit(void);

// slight improvement: replace " * sizeof(...)" by "<< ...SH"
#if !defined(LONGSH)
#define LONGSH (((sizeof(long)>>1)&1) + ((sizeof(long)>>2)&1)*2 + ((sizeof(long)>>3)&1)*3 + ((sizeof(long)>>4)&1)*4)
#endif

#if !defined(LLONGSH)
#define LLONGSH (((sizeof(long long)>>1)&1) + ((sizeof(long long)>>2)&1)*2 + ((sizeof(long long)>>3)&1)*3 + ((sizeof(long long)>>4)&1)*4) + ((sizeof(long long)>>5)&1)*5) + ((sizeof(long long)>>6)&1)*6) + ((sizeof(long long)>>7)&1)*7) + ((sizeof(long long)>>8)&1)*8)
#endif

#if !defined(PTRSH)
#define PTRSH (((sizeof(long *)>>1)&1) + ((sizeof(long *)>>2)&1)*2 + ((sizeof(long *)>>3)&1)*3 + ((sizeof(long *)>>4)&1)*4)
#endif

/* ------------------------------------------------------------------
   zzz <--> GAP conversion (zgap.c)
   ------------------------------------------------------------------ */

char *zftogap(FEL f);


/* ------------------------------------------------------------------
   Bitstring operations (zbitstr.c)
   ------------------------------------------------------------------ */

typedef struct
{
    Ushort id;	/* always = T_BITS */
    char dummy[sizeof(long)-sizeof(Ushort)];
    unsigned char buf[1];
} bitstring_t;

extern size_t bs_size;

void bs_print(bitstring_t *b);
char *bs_desc(bitstring_t *b);
void bs_setlen(int l);
void bs_reset(bitstring_t *x);
bitstring_t *bs_alloc(void);
bitstring_t *bs_dup(bitstring_t *s);
void bs_free(bitstring_t *b);
void bs_set(bitstring_t *b, int i);
void bs_clear(bitstring_t *b, int i);
int bs_test(bitstring_t *b, int i);
bitstring_t *bs_read(FILE *f);
int bs_write(FILE *f, bitstring_t *b);
void bs_and(bitstring_t *dest, bitstring_t *src);
void bs_minus(bitstring_t *dest, bitstring_t *src);
void bs_or(bitstring_t *dest, bitstring_t *src);
int bs_match(bitstring_t *x, bitstring_t *y);
int bs_issub(bitstring_t *a, bitstring_t *b);
int bs_cmp(bitstring_t *a, bitstring_t *b);
void bs_cpy(bitstring_t *a, bitstring_t *b);


/* ------------------------------------------------------------------
   File i/o (zfile.c)
   ------------------------------------------------------------------ */

size_t zreadlong(FILE *f, long *buf, size_t n);
size_t zwritelong(FILE *f, long *buf, size_t n);
size_t zreadvec(FILE *f, PTR buf, size_t n);
size_t zwritevec(FILE *f, PTR buf, size_t n);
int zseek(FILE *f, long pos);
FILE *zreadhdr(char *name, long *fld, long *nor, long *noc);
FILE *zwritehdr(char *name, long fld, long nor, long noc);



/* ------------------------------------------------------------------
   Gauss elimination and related functions (zgauss.c, znullsp.c,
   zmatinv.c)
   ------------------------------------------------------------------ */

int zmkpivot(PTR matrix, long nor, long *piv);
long zmkechelon(PTR matrix, long nor, long *piv);
int zcleanrow(PTR row, PTR matrix, long nor, long *piv);
int zcleanrow2(PTR row,PTR matrix,long nor,long *piv,PTR row2);
long znullsp(PTR matrix, long nor, long *piv, PTR nsp);
int zmatinv(PTR mat, PTR result);


/* ------------------------------------------------------------------
   Projection on the quotient (zquot.c)
   ------------------------------------------------------------------ */

int zquotinit(PTR subspace, long dim, long *piv);
int zquot(PTR space, long dim, PTR quot);
int zquotop(PTR matrix, PTR quot);


/* ------------------------------------------------------------------
   Seed vector generation (zpseed.c)
   ------------------------------------------------------------------ */

extern PTR zpseed_vec;		/* The seed vector */

void zpseed_free(void);
int zpseed_init(long sdim, PTR sbasis);
long zpseed_make(long num);
long zpseed_next(void);

/* ------------------------------------------------------------------
   Command line parsing (args.h)
   ------------------------------------------------------------------ */

typedef struct { char *name; char *shortdesc; char *rcsrev;
	char **helptext; } proginfo_t;

#define GETINT_ERR -12345
#define OPT_END -1

extern char opt_char;		/* Current option */
extern char opt_text[50];	/* Option text */
extern char *opt_text_ptr;	/* Current position in option text */
extern int opt_ind;		/* Index in argv[] list */
extern char MeatAxeBinDir[250];	/* MeatAxe program directory */

void initargs(int argc, char **argv, proginfo_t *pi);
int zgetopt(char *pattern);
long getint(void);



/* ------------------------------------------------------------------
   Messages (message.c)
   ------------------------------------------------------------------ */

extern int mtxerrno;
extern int mtxerraction;
void mtxerror(char *text);
/*
void errexit(int code, char *text);
int errhandler(int errno, char *errfile, int errline);
int Message(FILE *f, const char *fmt, ...);
int ErrorExit(const char *fmt, ...);
*/
void errexit(int, char *);
int errhandler(int, char *, int);
int Message(FILE *, const char *, ...);
int ErrorExit(const char *, ...);

#define MTXFAIL(errcode,retval) \
  { errhandler(errcode,__FILE__,__LINE__); return (retval); }
#define FATAL(msg)\
  (fprintf(stderr,"\n%s(%d): %s.\n",__FILE__,__LINE__,msg),exit(1))


extern int msg_level;
#define MSG0 (msg_level >= 0)
#define MSG1 (msg_level >= 1)
#define MSG2 (msg_level >= 2)
#define MSG3 (msg_level >= 3)
#define MESSAGE(level,args)\
  (msg_level>=(level) ? ( printf args , fflush(stdout), 1) : 0 )


/* ------------------------------------------------------------------
   CPU time (prtimes.c)
   ------------------------------------------------------------------ */

void prtimes(void);


/* ------------------------------------------------------------------
   Random numbers (random.c)
   ------------------------------------------------------------------ */

void RandInit(unsigned seed);
long int Random(void);
#define RandInt(max) ((unsigned int) (Random() % (max)))



/* ------------------------------------------------------------------
   Miscellaneous
   ------------------------------------------------------------------ */

long gcd(long a, long b);
long lcm(long a, long b);

/* ------------------------------------------------------------------
   Matrices
   ------------------------------------------------------------------ */

typedef struct
{
    Ushort id;			/* Always = T_MATRIX */
    long fl, nor, noc;		/* Field, #rows, #columns */
    PTR d;			/* Pointer to data area */
}
    matrix_t;

void matprint(char *name, matrix_t *p);
char *matdesc(matrix_t *s);
matrix_t *matalloc(long fl, long nor, long noc);
matrix_t *MTXmatid(long fl, long nor);
void matfree(matrix_t *m);

long matcmp(matrix_t *m1, matrix_t *m2);
matrix_t *matdup(matrix_t *src);
int  matmove(matrix_t *dest, matrix_t *src);
matrix_t *_matextract(matrix_t *src, long first, long n);
matrix_t *matread(FILE *f);
int matwrite(FILE *f, matrix_t *mat);
matrix_t *matload(char *fn);
int matsave(matrix_t *mat, char *fn);

matrix_t *matadd(matrix_t *dest, matrix_t *src);
matrix_t *matmul(matrix_t *dest, matrix_t *src);
int matmul_result(matrix_t *dest, matrix_t *src, matrix_t *res);
matrix_t *matmulF(matrix_t *src, FEL mark);
matrix_t *matsub(matrix_t *dest, matrix_t *src);
matrix_t *matneg(matrix_t *src);

matrix_t *mattr(matrix_t *src);
matrix_t *matinv(matrix_t *src);
int chkechelon(matrix_t *mat);
matrix_t *matpower(matrix_t *mat, long n);
long matorder(matrix_t *mat);

#if !defined(mat2str)
#define mat2str(m) ((char *)m->d)
#endif

#if !defined(zrowsize_io)
#define zrowsize_io zrowsize_io
#endif
#if !defined (zstr2row)
#define zstr2row(d,x) memcpy(d,x,zrowsize_io)
#endif
#if !defined(zrow2str)
#define zrow2str(d) ((char *)d)
#endif
// char *mat2str(matrix_t* m);
void str2mat(matrix_t* m, int l, char* x);

/* ------------------------------------------------------------------
   Higher-level gauss functions (gauss.c)
   ------------------------------------------------------------------ */

matrix_t *echelon(matrix_t *mat);
matrix_t *echelon_(matrix_t *mat);

long nullity(matrix_t *mat);
long nullity_(matrix_t *mat);
long nullity__(matrix_t *mat);

matrix_t *nullspace(matrix_t *mat);
matrix_t *nullspace_(matrix_t *mat);
matrix_t *nullspace__(matrix_t *mat);



/* ------------------------------------------------------------------
   ycomp.c
   ------------------------------------------------------------------ */

int spccomp(matrix_t *m1, matrix_t *m2, long n);
int spcequal(matrix_t *m1, matrix_t *m2);
int spccontains(matrix_t *m1, matrix_t *m2);


/* ------------------------------------------------------------------
   yspin.c
   ------------------------------------------------------------------ */

matrix_t *matspin(matrix_t *seed, int ngen, matrix_t *gen[]);
matrix_t *matspin_f(matrix_t *seed, int ngen, matrix_t *gen[],
	long *sdim);



/* ------------------------------------------------------------------
   Spin-up, split, and standard basis (zspin.c, zsbasis.c, spin.c,
   sbasis.c)
   ------------------------------------------------------------------ */

long zspinup(PTR space, long nseed, long *piv, int ngen, PTR gen[],
	int gentype);
int zsbasis(PTR seed, long nseed, int ngen, PTR gen[], PTR space,
	long *piv, PTR basis);

extern long *split_pivot;

/* Options */
#define SPL_SEED_MAKE	0x0000	/* Try all vectors in <seed> */
#define SPL_SEED_EACH	0x0001	/* Try vectors in <seed> one by one */
#define SPL_SEED_FIRST	0x0002	/* Take first seed vector */
#define SPL_SEED_SPACE	0x0003  /* Make closure of <seed> */
#define SPL_CONTINUE	0x0004  /* Continue */

/* Return codes */
#define SPL_FAILED	0  	/* Did not find an invariant subspace */
#define SPL_SUCCESS	1  	/* Has found an invariant subspace */
#define SPL_ERROR	-1	/* Error, see mtxerrno */

int spinup(matrix_t *seed,int ngen,matrix_t *gen[],int options,
	matrix_t **subspace);
int split(matrix_t *subspace, int ngen, matrix_t *gen[],
	matrix_t **sub, matrix_t **quot);
matrix_t *quotproj(matrix_t *subspace, matrix_t *vectors);
matrix_t *sbasis(matrix_t *seed, int ngen, matrix_t **gen);
int chbasis(matrix_t *basis, int ngen, matrix_t **gen,
	matrix_t **newgen);



/* ------------------------------------------------------------------
   Polynomials
   ------------------------------------------------------------------ */

typedef struct
{
    Ushort id;			/* Always = T_POLY */
    long fl;
    long deg;
    size_t size;  /* deg <= size-1 */
    FEL *buf;
}
poly_t;


char *poldesc(poly_t *s);
poly_t *polalloc(long fl, long degree);
void polfree(poly_t *x);
poly_t *poldup(poly_t *x);
poly_t *poladd(poly_t *dest, poly_t *src);
poly_t *polmul(poly_t *dest, poly_t *src);
poly_t *poldivmod(poly_t *a, poly_t *b);
poly_t *polmod(poly_t *a, poly_t *b);
void polprint(char *name, poly_t *p);
poly_t *polread(FILE *f);
int polwrite(FILE *f, poly_t *p);
int polcmp(poly_t *a, poly_t *b);
poly_t *polgcd(poly_t *a, poly_t *b);
poly_t *polderive(poly_t *p);
int vec2pol(PTR vec, poly_t *pol);
int pol2vec(poly_t *pol, PTR vec);
int polpack(poly_t *pol, PTR vec);
poly_t *polshiftmod(poly_t *p, long n, poly_t *q);

/* ------------------------------------------------------------------
   The word generator (words.h)
   ------------------------------------------------------------------ */

#define MAXFP 6            /* Standard fingerprint size */

typedef struct { int ngen; size_t len, max; matrix_t **b; } wgdata_t;
wgdata_t *WGInit(int ngen, matrix_t *gen[]);
int WGFree(wgdata_t *b);
matrix_t *MakeWord(wgdata_t *b, long n);
void makefp(wgdata_t *b, long fp[]);
char *SymbolicName(wgdata_t *b, long n);


/* ------------------------------------------------------------------
   Permutations
   ------------------------------------------------------------------ */

typedef struct
{
    Ushort id;			/* Always = T_PERM */
    long deg;
    PTR d;
} perm_t;

char *permdesc(perm_t *s);
void permprint(char *name, perm_t *x);
perm_t *permalloc(long deg);
void permfree(perm_t *m);
perm_t *permdup(perm_t *src);
perm_t *permmove(perm_t *dest, perm_t *src);
perm_t *permread(FILE *f);
int permwrite(FILE *f, perm_t *perm);
perm_t *permload(char *fn);
int permsave(perm_t *perm, char *fn);
perm_t *permmul(perm_t *dest, perm_t *src);
long permorder(perm_t *perm);
perm_t *permpower(perm_t *p, long n);


/* ------------------------------------------------------------------
   Insertion (matins.c)
   ------------------------------------------------------------------ */

matrix_t *matinsert(matrix_t *mat, poly_t *pol);
matrix_t *matinsert_(matrix_t *mat, poly_t *pol);


/* ------------------------------------------------------------------
   Factored polynomials (fpoly.c)
   ------------------------------------------------------------------ */

typedef struct {
    Ushort id;			/* Always T_FPOLY */
    size_t len, max;
    poly_t **p;			/* Irreducible factors */
    long *e;			/* Multiplicities */
} fpoly_t;


char *fpoldesc(fpoly_t *p);
void fpolprint(char *name, fpoly_t *p);
fpoly_t *fpolalloc(void);
fpoly_t *fpoldup(fpoly_t *s);
void fpolfree(fpoly_t *p);
fpoly_t *fpolread(FILE *f);
int fpolwrite(FILE *f, fpoly_t *p);
fpoly_t *fpolmulp(fpoly_t *dest, poly_t *src, long pwr);
fpoly_t *fpolmul(fpoly_t *dest, fpoly_t *src);


/* ------------------------------------------------------------------
   Characteristic and minimal polynomials (charpol.c, minpol.c)
   ------------------------------------------------------------------ */

extern long CharPolSeed;
poly_t *charpolfactor(matrix_t *mat);
fpoly_t *charpol(matrix_t *mat);
poly_t *minpolfactor(matrix_t *mat);
fpoly_t *minpol(matrix_t *mat);


/* ------------------------------------------------------------------
   Berlekamp factorization (berlekmp.c)
   ------------------------------------------------------------------ */

fpoly_t *factorization(poly_t *pol);



/* ------------------------------------------------------------------
   Sets (ysets.c)
   ------------------------------------------------------------------ */

typedef struct
{
    Ushort id;			/* Always = T_SET */
    size_t len, max;
    long *buf;
} set_t;

int set_allocstrategy(size_t first,size_t blocksize);
char *set_desc(set_t *s);
void set_print(char *name, set_t *x);
set_t *set_alloc(void);
set_t *set_dup(set_t *s);
void set_free(set_t *x);
int set_insert(set_t *set, long elem);
int set_contains(set_t *set, long elem);
set_t *set_read(FILE *f);
int set_write(FILE *f, set_t *set);


/* ------------------------------------------------------------------
   Sequences (sequence.c)
   ------------------------------------------------------------------ */

typedef struct
{
    Ushort id;			/* Always = T_SEQUENCE */
    size_t len, max;
    void **buf;
} sequence_t;

char *seq_desc(sequence_t *s);
void seq_print(char *name, sequence_t *s);
sequence_t *seq_alloc(size_t size);
sequence_t *seq_dup(sequence_t *s);
void seq_free(sequence_t *x);
int seq_insert(sequence_t *s, int pos, void *x);
int seq_remove(sequence_t *s, int pos);
sequence_t *seq_read(FILE *f);
int seq_write(FILE *f, sequence_t *x);

/* ------------------------------------------------------------------
   Integers and strings
   ------------------------------------------------------------------ */

typedef struct
{
    Ushort id;			/* Always = T_INT */
    long l;
} integer_t;

integer_t *intalloc(long l);
integer_t *intdup(integer_t *s);
char *intdesc(integer_t *s);
void intprint(char *name, integer_t *x);
void intfree(integer_t *x);
integer_t *intread(FILE *f);
int intwrite(FILE *f, integer_t *x);
integer_t *intadd(integer_t *d, integer_t *s);
integer_t *intsub(integer_t *d, integer_t *s);
integer_t *intmul(integer_t *d, integer_t *s);
integer_t *intdiv(integer_t *d, integer_t *s);
integer_t *intneg(integer_t *x);

typedef struct
{
    Ushort id;			/* Always = T_STR */
    char *s;
} string_t;

string_t *stringalloc(char *c);
string_t *stringdup(string_t *s);
char *stringdesc(string_t *s);
void stringprint(char *name, string_t *x);
void stringfree(string_t *x);
string_t *stringread(FILE *f);
int stringwrite(FILE *f, string_t *x);


/* ------------------------------------------------------------------
   MeatAxe object methods
   ------------------------------------------------------------------ */

void mtxfree(void *x);
void *mtxdup(void *x);
char *mtxgetname(void *x);
char *mtxgetdesc(void *x);
void *mtxread(FILE *f);
void mtxprint(void *x);
int mtxwrite(FILE *f, void *x);
void *mtxadd(void *l, void *r);
void *mtxsub(void *l, void *r);
void *mtxmul(void *l, void *r);
void *mtxdiv(void *l, void *r);
void *mtxpwr(void *l, void *r);
void *mtxneg(void *x);
void *mtxorder(void *x);


/* ------------------------------------------------------------------
   Profiling (profile.c)
   ------------------------------------------------------------------ */

#define PROFILE_BEGIN(var) long var = SClock();
#define PROFILE_END(var,cat) Prof##cat += SClock() - var;

extern long ProfFileIO;		/* File I/O */
extern long ProfNullSpace;	/* Matrix null space */
extern long ProfSpinUp;		/* Spin-up */
extern long ProfMakeWord;	/* Make word */
extern long ProfMatInsert;	/* Matrix insertion */
extern long ProfPolFactor;	/* Polynomial factorization */
extern long ProfCharPol;	/* Char. and minimal polynomial */

#endif	/* !defined(__MEATAXE_INCLUDED) */


