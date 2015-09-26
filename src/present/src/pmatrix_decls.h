/* ========================== Present =============================
   pmatrix_decls.h : Header file listing declarations in pmatrix.c

   (C) Copyright 1999-2000 David J. Green <green@math.uni-wuppertal.de>
   Department of Mathematics, University of Wuppertal,
   D-42097 Wuppertal, Germany
   This program is free software; see the file COPYING for details.
   ================================================================ */

Matrix_t *InnerRightAction(Matrix_t *dest, const Matrix_t *src, PTR scratch);
/* Guaranteed not to alter pointer dest->d */
/* Result will be assembled at scratch, then copied to dest */
/* This routine allocates NO memory */
Matrix_t *InnerLeftAction(const Matrix_t *src, Matrix_t *dest, PTR scratch);
/* Guaranteed not to alter pointer dest->d */
Matrix_t *InnerRightProduct(const Matrix_t *dest, const Matrix_t *src, PTR scratch);

int innerBasisChangeReg2Nontips(group_t *group, Matrix_t **matlist,
  long num, PTR workspace);
int innerBasisChangeNontips2Reg(group_t *group, Matrix_t **matlist,
  long num, PTR workspace);
int basisChangeReg2Nontips(group_t *group, Matrix_t **matlist, long num);
int changeActionMatricesReg2Nontips(group_t *group);
