/* ========================== C MeatAxe =============================
   berlekmp.c - Berlekamp factorization

   (C) Copyright 1993 Michael Ringe, Lehrstuhl D fuer Mathematik,
   RWTH Aachen, Germany  <mringe@tiffy.math.rwth-aachen.de>
   This program is free software; see the file COPYING for details.
   ================================================================== */


/* $Id: berlekmp.c,v 1.2 1997/09/11 15:42:33 gap Exp $
 *
 * $Log: berlekmp.c,v $
 * Revision 1.2  1997/09/11 15:42:33  gap
 * New version 2.2.3. AH
 *
 * Revision 1.10  1994/11/30  10:28:58  mringe
 * ANSI-C, Neue Random-Funktionen.
 *
 * Revision 1.9  1994/11/25  13:31:00  mringe
 * Neue Random...-Funktionen, ANSI C
 *
 * Revision 1.8  1994/07/28  06:04:43  mringe
 * zsetfield() und zsetlen() als getrennte Funktionen.
 *
 * Revision 1.7  1994/07/23  16:47:29  mringe
 * Neue null-space Funktionen
 *
 * Revision 1.6  1994/04/07  21:12:26  mringe
 * Benutzt fpoly_t.
 *
 * Revision 1.5  1994/03/14  12:59:28  mringe
 * Fehler beim Sortieren beseitigt.
 *
 * Revision 1.4  1994/03/14  09:44:28  mringe
 * polfactor() in factorization() umbenannt.
 *
 * Revision 1.3  1994/03/13  13:49:08  mringe
 * Erste lauffaehige Version.
 *
 */


#include <string.h>
#include <stdlib.h>
#include "meataxe.h"

typedef struct { poly_t *p; long n; } factor_t;

/* ------------------------------------------------------------------
   factorsquarefree() - Squarefree factorization.
   ------------------------------------------------------------------ */

static factor_t *factorsquarefree(poly_t *pol)

{
    long int e,j,k,ltmp,tdeg,exp,lexp;

    poly_t *t0, *t, *w, *v;
    FEL  *tbuf, *t0buf;
    factor_t  *list;
    int nfactors = 0;

    list = (factor_t *) malloc((pol->deg+1)*sizeof(factor_t));
    zsetfield(pol->fl);
    zsetlen(znoc);
    for (exp = 0, ltmp = zfl; ltmp % zchar == 0; ++exp, ltmp /= zchar);
    t0 = poldup(pol);
    e = 1;

    while ( t0->deg > 0 )
    {
	poly_t *der = polderive(poldup(t0));
        t = polgcd(t0,der);
	polfree(der);
        v = poldivmod(t0,t);
        polfree(t0); 
        for (k = 0; v->deg > 0; )
	{
	    poly_t *tmp;
	    if ( ++k % zchar == 0 )
	    {
		tmp = poldivmod(t,v);
              	polfree(t);
              	t = tmp;
	      	k++;
	    }
	    w = polgcd(t,v);
	    list[nfactors].p = poldivmod(v,w);
	    list[nfactors].n = e * k;
	    if (list[nfactors].p->deg > 0)
	       	++nfactors;			/* add to output */
	    else
	    	polfree(list[nfactors].p);	/* discard const. */
            polfree(v);
	    v = w;
	    tmp = poldivmod(t,v);
            polfree(t); 
            t = tmp; 
	} 
	polfree(v);

	/* shrink the polynomial */
      	tdeg = t->deg;
      	e *= zchar;
      	if ( tdeg % zchar != 0 )
	    printf("error in t, degree not div. by prime \n");
      	t0 = polalloc(zfl,tdeg/zchar);
      	t0buf = t0->buf;
      	tbuf = t->buf;
      	for (j = t0->deg; j >= 0; --j)
	{
	    FEL el, el1;
	    el = *tbuf;
	    tbuf += zchar;
	    el1 = el;
	    for (lexp = 0; lexp < exp-1; lexp++)
	      	el1 = zmul(el,el1);
	    *t0buf = el1;
	    ++t0buf;
	}
        polfree(t); 
    }
    polfree(t0);

    /* Terminate the list
       ------------------ */
    list[nfactors].p = NULL;
    list[nfactors].n = 0;
    return list;
}
		      


/* ------------------------------------------------------------------
   makekernel() - Determines the matrix of the frobenius and returns
   its nullspace.
   ------------------------------------------------------------------ */

static matrix_t *makekernel(poly_t *pol)

{
    matrix_t *materg;
    PTR rowptr,byteptr;
    FEL *xbuf, *pbuf = pol->buf;
    long pdeg = pol->deg;
    int k, xshift,idx;
    long fl = pol->fl;

    materg = matalloc(fl,pdeg,pdeg);
    rowptr = materg->d;

    xbuf = (FEL *) malloc((size_t) (pdeg+1) * sizeof(FEL));
    for (k = 0; k <= pdeg; ++k) xbuf[k] = F_ZERO;
    xbuf[0] = F_ONE;

    for (k = 0; k < pdeg; ++k)
    {
	int l;
        byteptr = rowptr;
        idx = 0;
	for (l = 0; l < pdeg; ++l) zinsert_step(&byteptr,&idx,xbuf[l]);
	zinsert(rowptr,k+1,zsub(xbuf[k],F_ONE));
	zsteprow(&rowptr);
        for (xshift = (int) fl; xshift > 0; )
	{
	    FEL f;
	    int d;

	    /* Find leading pos */
	    for (l = pdeg-1; xbuf[l] == F_ZERO && l >= 0; --l);

	    /* Shift left as much as possible */
	    if ((d = pdeg - l) > xshift) d = xshift;
	    for (; l >= 0; l--) xbuf[l+d] = xbuf[l];
	    for (l = d-1; l >= 0; --l) xbuf[l] = F_ZERO;
	    xshift -= d;
	    if (xbuf[pdeg] == F_ZERO) continue;

	    /* Reduce with pol */
	    f = zneg(zdiv(xbuf[pdeg],pbuf[pdeg]));
	    for (l = pdeg-1; l >= 0; --l)
		xbuf[l] = zadd(xbuf[l],zmul(pbuf[l],f));
	    xbuf[pdeg] = F_ZERO;
	}
    }
    free(xbuf);
    return nullspace__(materg);
 } 


/* ------------------------------------------------------------------
   berlekamp() - Find the irreducible factors of a squarefree
   polynomial.
   ------------------------------------------------------------------ */

static poly_t **berlekamp(poly_t *pol, matrix_t  *kernel)

{
    poly_t **list, **list2;
    int nfactors;
    PTR vec = kernel->d;
    int i, j;
    poly_t *t;

    //    list = (poly_t **) malloc((size_t)(kernel->nor+1)*sizeof(poly_t*));
    //    list2 = (poly_t **) malloc((size_t)(kernel->nor+1)*sizeof(poly_t*));
    list = (poly_t **) malloc((size_t)(kernel->nor+1) << PTRSH);
    list2 = (poly_t **) malloc((size_t)(kernel->nor+1) << PTRSH);
    list[0] = poldup(pol);
    nfactors = 1;
    t = polalloc(kernel->fl,kernel->noc-1);
    zsetlen(kernel->noc);

    /* Loop through all kernel vectors */
    for (j = 2; j <= kernel->nor; ++j)
    {
	int ngcd = 0;
	zsteprow(&vec);			/* Next vector */
	if (nfactors == kernel->nor) break;	/* Done? */
	for (i = 1; i <= kernel->noc; ++i)
	    t->buf[i-1] = zextract(vec,i);
	for (i = kernel->noc-1; t->buf[i] == F_ZERO; --i);
	t->deg = i;
	for (i = 0; i < nfactors; )
	{
	    long s;
	    if (list[i]->deg <= 1) {++i; continue;}
	    for (s = 0; s < zfl; ++s)
	    {
		poly_t *gcd;

		t->buf[0] = zitof(s);
		gcd = polgcd(list[i],t);
		if (gcd->deg >= 1)
		    list2[ngcd++] = gcd;
		else
		    polfree(gcd);
		if (nfactors == kernel->nor) break;	/* Done? */
	    }
	    if (ngcd > 0)
	    {
		int p;
		polfree(list[i]);
		for (p = i; p < nfactors -1; ++p)
		    list[p] = list[p+1];
		--nfactors;
	    }
	    else
		++i;
	    if (nfactors == kernel->nor) break;		/* Done? */
	}
	if (ngcd > 0)
	{
	    int p;
	    for (p = 0; p < ngcd; ++p)
	        list[nfactors++] = list2[p];
	}
    }
    polfree(t);
    free(list2);
    list[kernel->nor] = NULL;	/* Terminate the list */
    return list;
}




/* ------------------------------------------------------------------
   factorization() - Factorize a polynomial
   ------------------------------------------------------------------ */

fpoly_t *factorization(poly_t *pol)

{
    factor_t *list, *l;
    fpoly_t *factors;    
    PROFILE_BEGIN(t);

    factors = fpolalloc();
    list = factorsquarefree(pol);

    for (l = list; l->p != NULL; ++l)
    {
	matrix_t *kernel = makekernel(l->p);
	poly_t **irr = berlekamp(l->p,kernel), **i;

	matfree(kernel);
	for (i = irr; *i != NULL; ++i)
	{
	    fpolmulp(factors,*i,l->n);
	    polfree(*i);
	}
	free(irr);
	polfree(l->p);
    }
    free(list);
    PROFILE_END(t,PolFactor);
    return factors;
}

