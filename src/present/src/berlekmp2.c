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
 * FfSetField() und FfSetNoc() als getrennte Funktionen.
 *
 * Revision 1.7  1994/07/23  16:47:29  mringe
 * Neue null-space Funktionen
 *
 * Revision 1.6  1994/04/07  21:12:26  mringe
 * Benutzt FPoly_t.
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

typedef struct { Poly_t *p; long n; } factor_t;

/* ------------------------------------------------------------------
   factorsquarefree() - Squarefree factorization.
   ------------------------------------------------------------------ */

static factor_t *factorsquarefree(Poly_t *pol)

{
    long int e,j,k,ltmp,tdeg,exp,lexp;

    Poly_t *t0, *t, *w, *v;
    FEL  *tbuf, *t0buf;
    factor_t  *list;
    int nfactors = 0;

    list = (factor_t *) malloc((pol->deg+1)*sizeof(factor_t));
    FfSetField(pol->fl);
    FfSetNoc(FfNoc);
    for (exp = 0, ltmp = FfOrder; ltmp % FfChar == 0; ++exp, ltmp /= FfChar);
    t0 = poldup(pol);
    e = 1;

    while ( t0->deg > 0 )
    {
    Poly_t *der = polderive(poldup(t0));
        t = polgcd(t0,der);
    polfree(der);
        v = poldivmod(t0,t);
        polfree(t0);
        for (k = 0; v->deg > 0; )
    {
        Poly_t *tmp;
        if ( ++k % FfChar == 0 )
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
            ++nfactors;         /* add to output */
        else
            polfree(list[nfactors].p);  /* discard const. */
            polfree(v);
        v = w;
        tmp = poldivmod(t,v);
            polfree(t);
            t = tmp;
    }
    polfree(v);

    /* shrink the polynomial */
        tdeg = t->deg;
        e *= FfChar;
        if ( tdeg % FfChar != 0 )
        printf("error in t, degree not div. by prime \n");
        t0 = polalloc(FfOrder,tdeg/FfChar);
        t0buf = t0->buf;
        tbuf = t->buf;
        for (j = t0->deg; j >= 0; --j)
    {
        FEL el, el1;
        el = *tbuf;
        tbuf += FfChar;
        el1 = el;
        for (lexp = 0; lexp < exp-1; lexp++)
            el1 = FfMul(el,el1);
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

static Matrix_t *makekernel(Poly_t *pol)

{
    Matrix_t *materg;
    PTR rowptr;
    FEL *xbuf, *pbuf = pol->buf;
    long pdeg = pol->deg;
    int k, xshift,idx;
    long fl = pol->fl;

    materg = matalloc(fl,pdeg,pdeg);
    rowptr = materg->d;

    xbuf = (FEL *) malloc((size_t) (pdeg+1) * sizeof(FEL));
    for (k = 0; k <= pdeg; ++k) xbuf[k] = FF_ZERO;
    xbuf[0] = FF_ONE;

    for (k = 0; k < pdeg; ++k)
    {
    int l;
    idx = 0;
    for (; idx < pdeg; ++idx) FfInsert(rowptr,idx,xbuf[l]);
    FfInsert(rowptr,k+1,zsub(xbuf[k],FF_ONE));
    FfStepPtr(&rowptr);
        for (xshift = (int) fl; xshift > 0; )
    {
        FEL f;
        int d;

        /* Find leading pos */
        for (l = pdeg-1; xbuf[l] == FF_ZERO && l >= 0; --l);

        /* Shift left as much as possible */
        if ((d = pdeg - l) > xshift) d = xshift;
        for (; l >= 0; l--) xbuf[l+d] = xbuf[l];
        for (l = d-1; l >= 0; --l) xbuf[l] = FF_ZERO;
        xshift -= d;
        if (xbuf[pdeg] == FF_ZERO) continue;

        /* Reduce with pol */
        f = FfNeg(FfDiv(xbuf[pdeg],pbuf[pdeg]));
        for (l = pdeg-1; l >= 0; --l)
        xbuf[l] = FfAdd(xbuf[l],FfMul(pbuf[l],f));
        xbuf[pdeg] = FF_ZERO;
    }
    }
    free(xbuf);
    return nullspace__(materg);
 }


/* ------------------------------------------------------------------
   berlekamp() - Find the irreducible factors of a squarefree
   polynomial.
   ------------------------------------------------------------------ */

static Poly_t **berlekamp(Poly_t *pol, matrix_t  *kernel)

{
    Poly_t **list, **list2;
    int nfactors;
    PTR vec = kernel->d;
    int i, j;
    Poly_t *t;

    //    list = (Poly_t **) malloc((size_t)(kernel->nor+1)*sizeof(Poly_t*));
    //    list2 = (Poly_t **) malloc((size_t)(kernel->nor+1)*sizeof(Poly_t*));
    list = (Poly_t **) malloc((size_t)(kernel->nor+1) * sizeof(void*));
    list2 = (Poly_t **) malloc((size_t)(kernel->nor+1) * sizeof(void*));
    list[0] = poldup(pol);
    nfactors = 1;
    t = polalloc(kernel->fl,kernel->noc-1);
    FfSetNoc(kernel->noc);

    /* Loop through all kernel vectors */
    for (j = 2; j <= kernel->nor; ++j)
    {
    int ngcd = 0;
    FfStepPtr(&vec);         /* Next vector */
    if (nfactors == kernel->nor) break; /* Done? */
    for (i = 1; i <= kernel->noc; ++i)
        t->buf[i-1] = FfExtract(vec,i);
    for (i = kernel->noc-1; t->buf[i] == FF_ZERO; --i);
    t->deg = i;
    for (i = 0; i < nfactors; )
    {
        long s;
        if (list[i]->deg <= 1) {++i; continue;}
        for (s = 0; s < FfOrder; ++s)
        {
        Poly_t *gcd;

        t->buf[0] = FfFromInt(s);
        gcd = polgcd(list[i],t);
        if (gcd->deg >= 1)
            list2[ngcd++] = gcd;
        else
            polfree(gcd);
        if (nfactors == kernel->nor) break; /* Done? */
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
        if (nfactors == kernel->nor) break;     /* Done? */
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
    list[kernel->nor] = NULL;   /* Terminate the list */
    return list;
}




/* ------------------------------------------------------------------
   factorization() - Factorize a polynomial
   ------------------------------------------------------------------ */

FPoly_t *factorization(Poly_t *pol)

{
    factor_t *list, *l;
    FPoly_t *factors;
    PROFILE_BEGIN(t);

    factors = fpolalloc();
    list = factorsquarefree(pol);

    for (l = list; l->p != NULL; ++l)
    {
    Matrix_t *kernel = makekernel(l->p);
    Poly_t **irr = berlekamp(l->p,kernel), **i;

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

