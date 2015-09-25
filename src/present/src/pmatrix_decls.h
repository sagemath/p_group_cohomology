/* ========================== Present =============================
   pmatrix_decls.h : Header file listing declarations in pmatrix.c

   (C) Copyright 1999-2000 David J. Green <green@math.uni-wuppertal.de>
   Department of Mathematics, University of Wuppertal,
   D-42097 Wuppertal, Germany
   This program is free software; see the file COPYING for details.
   ================================================================ */

matrix_t *InnerRightAction(matrix_t *dest, const matrix_t *src, PTR scratch);
/* Guaranteed not to alter pointer dest->d */
/* Result will be assembled at scratch, then copied to dest */
/* This routine allocates NO memory */
matrix_t *InnerLeftAction(const matrix_t *src, matrix_t *dest, PTR scratch);
matrix_t *RightAction(matrix_t *dest, const matrix_t *src);
/* Guaranteed not to alter pointer dest->d */
void *InnerRightProduct(const matrix_t *dest, const matrix_t *src, PTR scratch);
/* Assembles dest * src at scratch. */
/* src should be square, scratch should point to enough space. */
matrix_t *RightProduct(const matrix_t *dest, const matrix_t *src);

void innerBasisChangeReg2Nontips(group_t *group, matrix_t **matlist,
  long num, PTR workspace);
void innerBasisChangeNontips2Reg(group_t *group, matrix_t **matlist,
  long num, PTR workspace);
void basisChangeReg2Nontips(group_t *group, matrix_t **matlist, long num);
void changeActionMatricesReg2Nontips(group_t *group);
