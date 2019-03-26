# -*- coding: utf-8 -*-

#*****************************************************************************
#
#    Explore graded isomorphisms of modular cohomology rings of finite groups
#
#    Copyright (C) 2019 Simon A. King <simon.king@uni-jena.de>
#
#    This file is part of p_group_cohomology.
#
#    p_group_cohomoloy is free software: you can redistribute it and/or modify
#    it under the terms of the GNU General Public License as published by
#    the Free Software Foundation, either version 2 of the License, or
#    (at your option) any later version.
#
#    p_group_cohomoloy is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#    GNU General Public License for more details.
#
#    You should have received a copy of the GNU General Public License
#    along with p_group_cohomoloy.  If not, see <http://www.gnu.org/licenses/>.
#*****************************************************************************

from sage.interfaces.singular import SingularElement
from sage.all import singular
from sage.misc.lazy_attribute import lazy_attribute
from sage.misc.cachefunc import cached_method
from pGroupCohomology import CohomologyRing
from sage.all import cartesian_product_iterator, Integer, Infinity
from sage.rings.polynomial.hilbert import first_hilbert_series
from pGroupCohomology.auxiliaries import coho_logger
import sys

#~ def GradedIsomorphism(A1,A2):
    #~ global cutoff, statistic_of_criteria
    #~ cutoff = 15
    #~ T = IsomorphismTest(A1,A2)
    #~ Tinv = IsomorphismTest(A2,A1)
    #~ while True:
        #~ print "Testing direct isomorphism"
        #~ result = T.explore_isomorphisms()
        #~ if result is not None:
            #~ statistic_of_criteria.append((bool(result),T._domain.GStem,T._codomain.GStem,cutoff,T.statistic))
            #~ return result
        #~ print "Testing inverse isomorphism"
        #~ result = Tinv.explore_isomorphisms()
        #~ if result is False:
            #~ statistic_of_criteria.append((bool(result),Tinv._domain.GStem,Tinv._codomain.GStem,cutoff,Tinv.statistic))
            #~ return False
        #~ if result is None:
            #~ cutoff *= 10
            #~ continue
        #~ Tinv._R_elim.set_ring()
        #~ result = [singular.eval('NF(@%s,%s)'%(x.name(),Tinv.urbild_GB.name())) for x in Tinv._codomain.Gen]
        #~ T.set_images(result)
        #~ assert T.is_isomorphism(), "Inverting the isomorphism didn't work!"
        #~ statistic_of_criteria.append((bool(result),Tinv._domain.GStem,Tinv._codomain.GStem,cutoff,Tinv.statistic))
        #~ return result


########################################################################
##
##  THE TEST ENGINE

class IsomorphismTest:
    def __init__(self, D, C, use_annihilator = True, use_radical = False, cutoff = 15, paranoic = False):
        self.paranoic = paranoic
        self.use_annihilator = use_annihilator
        self.use_radical = use_radical
        self.cutoff = cutoff
        self.total_candidates = Integer(0)
        self.critical_generators = [] # a generator that can't be mapped
        self.rigid_generators = [] # all generators which have a unique
                                   # candidate for mapping
        self.statistic = {}

        self._domain = D
        assert self._domain.completed, "%r ist not completely computed yet"%D
        self._codomain = C
        assert self._codomain.completed, "%r ist not completely computed yet"%C
        self.prefix = self._domain.prefix+self._codomain.prefix
        self.singular = singular
        self.singular.LIB('primdec')
        #
        self._SD = self.singular(self._domain)
        self._SD.set_ring()
        self.singular.eval('if(defined(%srelation_ideal)>0){kill %srelation_ideal;}'%(self.prefix,self.prefix))
        self.singular.eval('ideal %srelation_ideal = ringlist(basering)[4]'%self.prefix)
        self.singular.eval('if(defined(%smapI)>0){kill %smapI;}'%(self.prefix,self.prefix))
        self.singular.eval('ideal %smapI'%self.prefix)
        #
        self._SC = self.singular(self._codomain)
        self._SC.set_ring()
        self.singular.eval('if(defined(%smapI)>0){kill %smapI;}'%(self.prefix,self.prefix))
        self.singular.eval('ideal %smapI'%self.prefix)
        L = self._SC.ringlist()
        tmpIC = L[4]
        self._codomain_comm = self.singular('ring(list(%s[1..3],ideal(0)))'%(L.name()))
        i = self.singular._next_var_name()
        self.singular.eval('for (int %s=1; %s<=size(%s[2]); %s++){%s[2][%s]="@"+%s[2][%s];} kill %s;'%(i,i,L.name(),i,L.name(), i,L.name(),i,i))
        if self._domain.base_ring().characteristic()%2:
            self.singular.LIB("filterregular.lib")
            self.singular.LIB("poly.lib")
            self._dim_command = 'GKdim'
            #self._R_elim = self.singular('gcRingSum(ring(%s))+%s'%(L.name(),self._SD.name()))
        else:
            self._dim_command = 'dim'
        self._R_elim = self.singular('ring(%s)+%s'%(L.name(),self._SD.name()))
        self._SC.set_ring()
        self.singular.eval('kill '+L.name())
        #self._R_elim.set_ring()
        #
        # First, we create a NON-COMMUTATIVE UNQUOTIENTED version of the domain ring.
        # We only want to see the trivial relations.
        self._domain.set_ring()
        R = self.singular('basering')
        L = self.singular.ringlist('basering')
        tmpID = L[4]
        # Now, we create COMMUTATIVE UNQUOTIENTED versions of the ring
        self._domain_comm = self.singular('ring(list(%s[1..3],ideal(0)))'%(L.name()))
        self.singular.eval('kill '+L.name())
        self._domain_comm.set_ring()
        # "qrels" are *only* the trivial relations in a supercommutative ring!
        self.singular.eval('if(defined(qrels)>0){kill qrels;}')
        self.singular.eval('ideal qrels = imap(%s, %s)'%(R.name(), tmpID.name()))
        self.singular.eval('if(defined(%sfetchI)>0){kill %sfetchI;}'%(self.prefix,self.prefix))
        self.singular.eval('ideal %sfetchI'%self.prefix)
        R.set_ring()
        self.singular.eval('kill '+tmpID.name())

        #
        self._codomain_comm.set_ring()
        # This time, the quotient relations include the non-trivial relations too.
        self.singular.eval('if(defined(qrels)>0){kill qrels;}')
        self.singular.eval('ideal qrels = imap(%s, %s)'%(self._SC.name(), tmpIC.name()))
        self.singular.eval('if(defined(%sfetchI)>0){kill %sfetchI;}'%(self.prefix,self.prefix))
        self.singular.eval('ideal %sfetchI'%self.prefix)
        self._SC.set_ring()
        self.singular.eval('kill '+tmpIC.name())

    def __repr__(self):
        return "IsomorphismTest(%r, %r)"%(self._domain, self._codomain)

    def elements(self, d):
        # iterate over non-zero indecomposable degree-d elements of the codomain
        # as a string
        S = self._codomain.standard_monomials(d)
        ch = self._codomain.base_ring().characteristic()
        coho_logger.debug("test up to {}^{} = {} elements".format(ch,len(S),ch**len(S)), self)
        counter = 0
        for C in cartesian_product_iterator([range(ch)]*len(S)):
            counter += 1
            if any(C):
                #print ".",
                sys.stdout.flush()
                indecomposable = False
                for c,s in zip(C,S):
                    if c and not ('*' in s):
                        indecomposable = True
                        break
                #print "indecomposable"
                if indecomposable:
                    yield '+'.join([repr(c)+'*'+s for c,s in zip(C,S) if c])

    def explore_isomorphisms(self):
        coho_logger.info("Trying to find an isomorphism", self)
        self.clear_candidates()
        self.exhaustive = True
        self.not_exhausted_generators = set([])
        orig_gens = [(x.rdeg(), x.ydeg(), x.deg(), i+1) for i,x in enumerate(self._domain.Gen) if not x.rdeg()]
        orig_gens.sort() # heuristic: those which come first are more likely to be rigid.
        while True:
            n_rigids = len(self.rigid_generators)
            raw_Sizes = []
            for rdeg,ydeg,deg,nb in orig_gens:
                raw_Sizes.append((len(self.candidates_of_gens((nb,),len(self.rigid_generators))), rdeg, ydeg, deg, nb))
            if len(self.rigid_generators)==n_rigids:
                break
        raw_Sizes.sort()
        Rigids = []
        Sizes = []
        CutBranches = []
        coho_logger.debug("iterating over %d raw sizes", self, len(raw_Sizes))
        for (l,r,y,d,g) in raw_Sizes:
            if l==1:
                Rigids.append((r,y,d,l,g))
            elif g in self.not_exhausted_generators:
                CutBranches.append((r,y,d,l,g))
            else:
                Sizes.append((r,y,d,l,g))
        Sizes = Rigids+Sizes+CutBranches
        Regs = []
        Knowns = [p[4] for p in Sizes]
        for i,x in enumerate(self._domain.Gen):
            if x.rdeg():
                if i+1 not in Knowns:
                    Regs.append((x.deg(),0,0,0, i+1))
        Regs.sort()
        Sizes.extend(Regs)
        coho_logger.debug("now determining candidates for %d elements", self, len(Sizes))
        Cands = self.candidates_of_gens(tuple([p[4] for p in Sizes]),len(self.rigid_generators))
        if Cands:
            coho_logger.info("Isomorphism found!", self)
            return Cands[0]
        if self.exhaustive or self.critical_generators:
            coho_logger.info("There is definitely no isomorphism", self)
            return False
        coho_logger.info("No conclusion on the existence of an isomorphism.", self)

    def clear_candidates(self):
        clear_list = [k for k in self.candidates_of_gens.cache.iterkeys() if k[0][-1] and any([e in self.not_exhausted_generators for e in k[0][0]])]
        for k in clear_list:
            del self.candidates_of_gens.cache[k]

    @cached_method
    def candidates_of_gens(self, Gens, number_of_rigids, allow_cutoff = True):
        C = []
        counter = 0
        if self.candidates_of_gens.is_in_cache(Gens, number_of_rigids, False):
            return self.candidates_of_gens(Gens, number_of_rigids, False)
        Rigids = []
        try:
            if self.critical_generators:
                coho_logger.info("There cannot be a homomorphism, (%s) cannot be mapped"%', '.join(['gen(%d)'%k for k in self.critical_generators]), self)
                return []
            if len(Gens)==1:
                i = Gens[0]
                old_candidates = None
                for nb_rig in range(number_of_rigids):
                    if self.candidates_of_gens.is_in_cache(Gens, nb_rig):
                        old_candidates = self.candidates_of_gens(Gens, nb_rig)
                        break
                if old_candidates is not None:
                    if not old_candidates:
                        return old_candidates
                else:
                    nil_deg = self._domain.gen(i).nilpotency_degree()
                Ims = [0]*len(self._domain.Gen)
                for g in self.rigid_generators:
                    if i==g[0]:
                        Ims[i-1] = g[1]
                        return [tuple(Ims)]
                    Ims[g[0]-1] = g[1]
                    if g[0] not in Gens:
                        Rigids.append(g[0])
                # Heuristic: Generally, "regular" generators (that form a
                # regular sequence) will have many possible images---here is
                # where the size of the ring's automorphism group may become
                # problematic. So, we may cut the candidate list short.
                for y in old_candidates or self.elements(self._domain.gen(i).deg()):
                    if (not old_candidates):
                        if self._codomain(y).nilpotency_degree()!=nil_deg:
                            self.statistic['nil-deg'] = self.statistic.get('nil-deg',0) + 1
                            continue
                        if self.rigid_generators:
                            # Could be that computing annihilator is easier
                            # with just a single element...
                            ShortIms = [0]*len(self._domain.Gen)
                            ShortIms[i-1] = y
                            if not self.potential_partial_isomorphism(ShortIms):
                                continue
                        Ims[i-1] = y
                    else:
                        Ims[i-1] = y[i-1]
                    if self.potential_partial_isomorphism(Ims):
                        counter += 1
                        C.append(tuple(Ims))
                        if allow_cutoff and (counter >= (6 if not self.rigid_generators else 3)*self.cutoff):
                            coho_logger.debug("cutting list of nonzero elements", self)
                            self.not_exhausted_generators.add(i)
                            self.exhaustive = False
                            break
                if not C and not any([k in self.not_exhausted_generators for k in Gens]):
                    if not self.critical_generators:
                        self.critical_generators = list(Gens)
                    else:
                        self.critical_generators.append(i)
                if len(C)==1:
                    if Gens[0] not in [r[0] for r in self.rigid_generators]:
                        coho_logger.info("gen(%d) is rigid: %s --> %s"%(Gens[0],self._domain.gen(Gens[0]).name(),C[0][Gens[0]-1]), self)
                        self.rigid_generators.append((Gens[0],C[0][Gens[0]-1]))
                if not i in self.not_exhausted_generators:
                    self.candidates_of_gens.set_cache(C, Gens, number_of_rigids, False)
                return C
            h1 = -1 #len(Gens)//2
            h2 = h1 #-1 if len(Gens)<=2 else (-2 if len(Gens)==3 else -3)
            FirstHalf = self.candidates_of_gens(Gens[:h1],len(self.rigid_generators))
            if FirstHalf:
                SecondHalf = self.candidates_of_gens(Gens[h1:],len(self.rigid_generators))
                #~ coho_logger.info("Testing up to %d*%d = %d assignments"%(len(FirstHalf),len(SecondHalf), len(FirstHalf)*len(SecondHalf)), self)
            else:
                SecondHalf = []
                coho_logger.info("No candidates remain", self)
            self.remove_partial_relations_from_cache(len(Gens))
            self.remove_candidates_from_cache(len(Gens))
            for Ims1,Ims2 in cartesian_product_iterator([FirstHalf, SecondHalf]):
                Ims = [None if (0!=a!=b!=0) else (a if a else b) for a,b in zip(Ims1,Ims2)]
                for g in self.rigid_generators:
                    if 0!=Ims[g[0]-1]!=g[1]:
                        raise RuntimeError("Value of rigid generator is not assumed")
                    else:
                        Ims[g[0]-1] = g[1]
                        if g[0] not in Gens:
                            Rigids.append(g[0])
                if None in Ims:
                    continue
                if (0 in Ims and len(set(Ims))-1<len(Ims)-Ims.count(0)) or (0 not in Ims and len(set(Ims))<len(Ims)-Ims.count(0)):
                    self.statistic['triviality'] = self.statistic.get('triviality',0) + 1
                    continue
                if self.potential_partial_isomorphism(Ims):
                    counter += 1
                    C.append(tuple(Ims))
                    if len(Gens)==len(self._domain.Gen):
                        return C
                    if allow_cutoff and (counter >= self.cutoff*(2**(len(Ims)-Ims.count(0)-len(self.rigid_generators)-1))):
                        coho_logger.debug("cutting list of candidates", self)
                        for k in Gens:
                            self.not_exhausted_generators.add(k)
                        self.exhaustive = False
                        break
            if len(C)==1:
                old_rigids = [x[0] for x in self.rigid_generators]
                for g in Gens:
                    if g not in old_rigids:
                        self.rigid_generators.append((g,C[0][g-1]))
                        coho_logger.info("further rigid generator gen(%d) --> %s"%(g,C[0][g-1]), self)
            if not C and not any([k in self.not_exhausted_generators for k in Gens]):
                if not self.critical_generators:
                    self.critical_generators = list(Gens)
                else:
                    self.critical_generators.extend(Gens)
            coho_logger.info("%d potential assignments for %r",self, len(C), ["gen(%d)"%g for g in Gens])
            if all(k not in self.not_exhausted_generators for k in Gens):
                self.candidates_of_gens.set_cache(C, Gens, number_of_rigids, False)
                if Rigids:
                    self.candidates_of_gens.set_cache(C, tuple(Rigids)+Gens, number_of_rigids, False)
            if allow_cutoff and Rigids:
                self.candidates_of_gens.set_cache(C, tuple(Rigids)+Gens, number_of_rigids, True)
            return C
        finally:
            pass

    @lazy_attribute
    def unquotiented_domain(self):
        self._domain.set_ring()
        L = self.singular('ringlist(basering)')
        self.singular.eval('%s[4]=ideal(0)'%L.name())
        R = L.ring()
        singular.eval('kill %s'%L.name())
        R.set_ring()
        self.singular.eval('if(defined(%selimI)>0){kill %selimI;}'%(self.prefix,self.prefix))
        self.singular.eval('ideal %selimI'%self.prefix)
        return R

    def remove_partial_relations_from_cache(self, n):
        """
        Remove cached partial relations for all subrings of less than n generators
        """
        keys = [k for k in self.partial_relations.cache.iterkeys() if k[0][0].count(True)<n]
        for k in keys:
            del self.partial_relations.cache[k]
        keys = [k for k in self.partial_relations.cache.iterkeys() if k[0][0].count(True)<n]

    def remove_candidates_from_cache(self, n):
        """
        Remove image candidates for all sets of less than or equal n and more
        than 1 generators. This also removes cached Hilbert data.

        Compare .clear_candidates(), which removes everything that has been cut!
        """
        keys = [k for k in self.candidates_of_gens.cache.iterkeys() if 1<len(k[0][0])<=n]
        keys = [k for k in self.hilbert_of_preimage.cache.iterkeys() if len(k[0][0])<=n]
        for k in keys:
            del self.hilbert_of_preimage.cache[k]
        keys = [k for k in self.hilbert_of_preimage_annihilator.cache.iterkeys() if len(k[0][0])<=n]
        for k in keys:
            del self.hilbert_of_preimage_annihilator.cache[k]
        keys = [k for k in self.hilbert_of_preimage_radical.cache.iterkeys() if len(k[0][0])<=n]
        for k in keys:
            del self.hilbert_of_preimage_radical.cache[k]

    @cached_method
    def partial_relations(self,T):
        self.unquotiented_domain.set_ring()
        H1 = self._domain
        self.singular.eval('%selimI=eliminate(imap(%sr(%d), %sI),%s)'%(self.prefix,H1.prefix,H1.knownDeg,H1.prefix, '*'.join([H1.gen(i+1).name() for i,x in enumerate(T) if not x])))
        self._SD.set_ring()
        return self.singular('imap(%s,%selimI)'%(self.unquotiented_domain.name(),self.prefix))

    def set_images(self, im_gens):
        self.total_candidates += 1
        if len(im_gens)!=len(self._domain.Gen):
            raise ValueError("%d generators, but %d images are given"%(len(self._domain.Gen),len(im_gens)))
        self._im_gens = im_gens
        self._SC.set_ring()
        if hasattr(self,'_Smap'):
            self.singular.eval('kill %s'%self._Smap.name())
            self.singular.eval('map %s = %s, ideal(%s)'%(self._Smap.name(), self._SD.name(), ','.join([str(x) for x in im_gens])))
        else:
            self._Smap = SingularElement(self.singular,'map','%s, ideal(%s)'%(self._SD.name(), ','.join([str(x) for x in im_gens])))
        self._codomain_comm.set_ring()
        self._R_elim.set_ring()
        try:
            if 'urbild_GB' in self.__dict__:
                self.singular.eval('kill %s'%(self.urbild_GB.name()))
                del self.__dict__['urbild_GB']
        except BaseException:
            pass
        if 'hilbert_of_image' in self.__dict__:
            del self.__dict__['hilbert_of_image']
        if 'hilbert_of_image_radical' in self.__dict__:
            del self.__dict__['hilbert_of_image_radical']
        if 'hilbert_of_image_annihilator' in self.__dict__:
            del self.__dict__['hilbert_of_image_annihilator']
        if hasattr(self, '_J_elim'):
            self.singular.eval('%s = ideal(matrix(ideal(fetch(%s,%s)))-matrix(ideal(%s)))'%(self._J_elim.name(), self._SC.name(),self._Smap.name(),self.singular.eval('varstr(%s)'%self._SD.name())))
        else:
            self._J_elim = self.singular('ideal(matrix(ideal(fetch(%s,%s)))-matrix(ideal(%s)))'%(self._SC.name(),self._Smap.name(),self.singular.eval('varstr(%s)'%self._SD.name())))
        self._SC.set_ring()

########
##
##   Hilbert functions of the ideal generated by some generators resp. their images must coincide.

    @lazy_attribute
    def hilbert_of_image(self):
        self._SC.set_ring()
        #--tmpI = self._Smap.ideal().std()
        self.singular.eval('%smapI = std(ideal(%s))'%(self.prefix,self._Smap.name()))
        self._codomain_comm.set_ring()
        # qrels contains *all* quotient relations, including the nontrivials.
        #--tmpI2 = self.singular('fetch(%s,%s)+qrels'%(self._SC.name(),tmpI.name()))
        self.singular.eval('%sfetchI = fetch(%s,%smapI)+qrels'%(self.prefix,self._SC.name(),self.prefix))
        self.singular.eval('attrib(%sfetchI,"isSB",1)'%self.prefix)
        return first_hilbert_series(self.singular('%sfetchI'%(self.prefix)), self._codomain.degvec)

    @lazy_attribute
    def hilbert_of_image_annihilator(self):
        self._SC.set_ring()
        #--tmpI = self._Smap.ideal().std()
        ActiveGens = [i for i,x in enumerate(self._im_gens) if x]
        if ActiveGens:
            d = [self._codomain.Gen[i].deg() for i in ActiveGens]
            SmallerGens = ','.join([x.name() for x in self._codomain.Gen if x.deg()<d])
            if not SmallerGens:
                SmallerGens = 0
        else:
            SmallerGens = 0
        self.singular.eval('%smapI = std(ideal(%s)+ideal(%s))'%(self.prefix,SmallerGens,self._Smap.name()))
        self.singular.eval('%smapI = std(quotient(std(0),%smapI))'%(self.prefix,self.prefix))
        self._codomain_comm.set_ring()
        # qrels contains *all* quotient relations, including the nontrivials.
        self.singular.eval('%sfetchI = fetch(%s,%smapI)+qrels'%(self.prefix,self._SC.name(),self.prefix))
        self.singular.eval('attrib(%sfetchI,"isSB",1)'%self.prefix)
        return first_hilbert_series(self.singular('%sfetchI'%(self.prefix)), self._codomain.degvec)

    @lazy_attribute
    def hilbert_of_image_radical(self):
        self._SC.set_ring()
        #--tmpI = self._Smap.ideal().std()
        self.singular.eval('%smapI = std(ideal(%s))'%(self.prefix,self._Smap.name()))
        self.singular.eval('%smapI = std(radical(%smapI))'%(self.prefix,self.prefix))
        self._codomain_comm.set_ring()
        # qrels contains *all* quotient relations, including the nontrivials.
        self.singular.eval('%sfetchI = fetch(%s,%smapI)+qrels'%(self.prefix,self._SC.name(),self.prefix))
        self.singular.eval('attrib(%sfetchI,"isSB",1)'%self.prefix)
        return first_hilbert_series(self.singular('%sfetchI'%(self.prefix)), self._codomain.degvec)

    @cached_method
    def hilbert_of_preimage(self, Gens):
        self._SD.set_ring()
        #--tmpI = self.singular('std(ideal(%s))'%(','.join(['var(%d)'%i for i in Gens])))
        self.singular.eval('%smapI = std(ideal(%s))'%(self.prefix,','.join(['var(%d)'%i for i in Gens])))
        self._domain_comm.set_ring()
        # qrels only contains the "trivial" relations a^2=0. That's why above we now add the nontrivials...
        self.singular.eval('%sfetchI = fetch(%s,%smapI)+qrels+imap(%sr(%d),%sI)'%(self.prefix,self._SD.name(),self.prefix,self._domain.prefix,self._domain.knownDeg,self._domain.prefix))
        self.singular.eval('attrib(%sfetchI,"isSB",1)'%self.prefix)
        return first_hilbert_series(self.singular('%sfetchI'%(self.prefix)), self._domain.degvec)

    @cached_method
    def hilbert_of_preimage_annihilator(self, Gens):
        self._SD.set_ring()
        d = [self._domain.Gen[i-1].deg() for i in Gens]
        SmallerGens = ','.join([x.name() for x in self._domain.Gen if x.deg()<d])
        if not SmallerGens:
            SmallerGens = 0
        #--tmpI = self.singular('std(ideal(%s))'%(','.join(['var(%d)'%i for i in Gens])))
        self.singular.eval('%smapI = std(ideal(%s)+ideal(%s))'%(self.prefix, SmallerGens,','.join(['var(%d)'%i for i in Gens])))
        self.singular.eval('%smapI = std(quotient(std(0),%smapI))'%(self.prefix,self.prefix))
        self._domain_comm.set_ring()
        # qrels only contains the "trivial" relations a^2=0. That's why above we now add the nontrivials...
        self.singular.eval('%sfetchI = fetch(%s,%smapI)+qrels+imap(%sr(%d),%sI)'%(self.prefix,self._SD.name(),self.prefix,self._domain.prefix,self._domain.knownDeg,self._domain.prefix))
        self.singular.eval('attrib(%sfetchI,"isSB",1)'%self.prefix)
        return first_hilbert_series(self.singular('%sfetchI'%(self.prefix)), self._domain.degvec)

    @cached_method
    def hilbert_of_preimage_radical(self, Gens):
        self._SD.set_ring()
        #--tmpI = self.singular('std(ideal(%s))'%(','.join(['var(%d)'%i for i in Gens])))
        self.singular.eval('%smapI = std(ideal(%s))'%(self.prefix,','.join(['var(%d)'%i for i in Gens])))
        self.singular.eval('%smapI = std(radical(%smapI))'%(self.prefix,self.prefix))
        self._domain_comm.set_ring()
        # qrels only contains the "trivial" relations a^2=0. That's why above we now add the nontrivials...
        self.singular.eval('%sfetchI = fetch(%s,%smapI)+qrels+imap(%sr(%d),%sI)'%(self.prefix,self._SD.name(),self.prefix,self._domain.prefix,self._domain.knownDeg,self._domain.prefix))
        self.singular.eval('attrib(%sfetchI,"isSB",1)'%self.prefix)
        return first_hilbert_series(self.singular('%sfetchI'%(self.prefix)), self._domain.degvec)

    @lazy_attribute
    def urbild_GB(self):
        coho_logger.debug(">>> need elimination...", self)
        self._R_elim.set_ring()
        return self._J_elim.groebner()

    def is_homomorphism(self):
        self._SD.set_ring()
        self._SC.set_ring()
        return self.singular.eval('size(NF(%s(%srelation_ideal),std(0)))'%(self._Smap.name(),self.prefix))=='0'

    def potential_partial_isomorphism(self, im_gens):
        new_im_gens = list(im_gens)
        self.set_images(new_im_gens)
        counter = self.statistic.get(('potential isomorphism',len(im_gens)-im_gens.count(0)),0) + 1
        self.statistic['potential isomorphism',len(im_gens)-im_gens.count(0)] = counter
        sys.stdout.flush()
        if all(im_gens):
            return self.is_isomorphism()
        if not self.paranoic:
            # Do the Hilbert functions match? If they don't, it can't
            # become an isomorphism.
            HIm = self.hilbert_of_image
            HPrim = self.hilbert_of_preimage(tuple([i+1 for i,x in enumerate(new_im_gens) if x]))
            if HIm!=HPrim:
                self.statistic["Poincare series of ideals do not match"] = self.statistic.get("Poincare series of ideals do not match", 0) + 1
                return False

        if len(im_gens)-im_gens.count(0)>1:
            # For single generators, we would just test the nilpotency degree,
            # but this has already been considered.
            QD = self.partial_relations(tuple(bool(x) for x in new_im_gens))
            self._SC.set_ring()
            if self.singular.eval('size(NF(%s(%s),std(0)))'%(self._Smap.name(),QD.name()))!='0':
                self.statistic["Subalgebras do not match"] = self.statistic.get("Subalgebras do not match",0) + 1
                return False

        if self.use_annihilator:
            HIm = self.hilbert_of_image_annihilator
            HPrim = self.hilbert_of_preimage_annihilator(tuple([i+1 for i,x in enumerate(new_im_gens) if x]))
            if HIm!=HPrim:
                self.statistic["Poincare series of annihilators do not match"] = self.statistic.get("Poincare series of annihilators do not match", 0) + 1
                return False
        if self.use_radical:
            HIm = self.hilbert_of_image_radical
            HPrim = self.hilbert_of_preimage_radical(tuple([i+1 for i,x in enumerate(new_im_gens) if x]))
            if HIm!=HPrim:
                self.statistic["Poincare series of radicals do not match"] = self.statistic.get("Poincare series of radicals do not match", 0) + 1
                return False
        return True

    def is_isomorphism(self):
        self.statistic['isomorphism test'] = self.statistic.get('isomorphism test',0)+1
        if self._domain.poincare_series()!=self._codomain.poincare_series():
            coho_logger.info(">>> Poincaré series do not match", self)
            return False
        coho_logger.info("Verify if we found an isomorphism", self)
        if not self.is_homomorphism():
            coho_logger.info(">>> Not a homomorphism", self)
            self.statistic["not homomorphism"] = self.statistic.get("not homomorphism",0)+1
            return False
        self._R_elim.set_ring()
        GL = [repr(m) for m in self.urbild_GB.lead()]
        # Since the Poincare series are equal,
        # we do not need to test both surjectivity
        # *and* injectivity---one of them is enough.
        ##
        # Contract: No generator name of the domain starts with
        # an '@'. Hence, if '@'+x.name() is in G for all generators
        # x of the codomain, we are gold.
        for x in self._codomain.Gen:
            if '@'+x.name() not in GL:
                #print x.name(),"is not in the image"
                coho_logger.info(">>> Homomorphism is not surjective", self)
                coho_logger.debug(">>> %s is not in the image", self, x.name())
                self.statistic["not surjective"] = self.statistic.get("not surjective",0) + 1
                return False
        return True


#~ def TheTest():
    #~ H1 = CohomologyRing(27,3)
    #~ H1.make()
    #~ H2 = CohomologyRing(81,9)
    #~ H2.make()
    #~ X = IsomorphismTest(H1,H2)
    #~ ndegs = [x.nilpotency_degree() for x in H1.Gen]
    #~ Im4to9 = []
    #~ for c4,c5,c6,c7,c8,c9 in cartesian_product_iterator([[1,2]]*6):
        #~ im4 = c4*H2.gen(4)
        #~ im5 = c5*H2.gen(5)
        #~ im6 = c6*H2.gen(6)
        #~ im7 = c7*H2.gen(7)
        #~ im8 = c8*H2.gen(8)
        #~ im9 = c9*H2.gen(9)
        #~ print [x.name() for x in [im4,im5,im6,im7,im8,im9]]
        #~ if X.potential_partial_isomorphism([0,0,0, im4, im5, im6, im7, im8, im9]):
            #~ Im4to9.append((im4,im5,im6,im7,im8,im9))
        #~ else:
            #~ print "cannot be extended"
    #~ return Im4to9
    #~ Im1and4to9 = []
    #~ for c1 in cartesian_product_iterator([[0,1,2],[0,1,2],[0,1,2]]):
        #~ if c1.count(0)==3:
            #~ continue
        #~ im1 = c1[0]*H2.gen(1)+c1[1]*H2.gen(2)+c1[2]*H2.gen(3)
        #~ if im1.nilpotency_degree()!=ndegs[0]:
            #~ print "ndeg of 1st image doesn't match"
            #~ continue
        #~ print "NEU",im1
        #~ for im4,im5,im6,im7,im8,im9 in Im4to9:
            #~ print [x.name() for x in [im4,im5,im6,im7,im8,im9]]
            #~ if X.potential_partial_isomorphism([im1,0,0, im4, im5, im6, im7, im8, im9]):
                #~ Im1and4to9.append((im1,im4, im5, im6, im7, im8, im9))
            #~ else:
                #~ print 'cannot be extended'
    #~ return Im1and4to9
    #~ Im2 = []
    #~ for c2 in cartesian_product_iterator([[0,1,2],[0,1,2],[0,1,2]]):
        #~ if c2.count(0)==3:
            #~ continue
        #~ im2 = c2[0]*H2.gen(1)+c2[1]*H2.gen(2)+c2[2]*H2.gen(3)
        #~ if im2.nilpotency_degree()!=ndegs[1]:
            #~ print "ndeg of 2nd image doesn't match"
            #~ continue
        #~ if X.potential_partial_isomorphism([0,im2]+[0]*7):
            #~ Im2.append(im2)
        #~ else:
            #~ print c1,'cannot be extended'
    #~ Im3 = []
    #~ for c3 in cartesian_product_iterator([[0,1,2],[0,1,2],[0,1,2]]):
        #~ if c3.count(0)==3:
            #~ continue
        #~ im3 = c3[0]*H2.gen(1)+c3[1]*H2.gen(2)+c3[2]*H2.gen(3)
        #~ if im3.nilpotency_degree()!=ndegs[2]:
            #~ print "ndeg of 3d image doesn't match"
            #~ continue
        #~ if X.potential_partial_isomorphism([0, 0, im3]+[0]*6):
            #~ Im3.append(im3)
        #~ else:
            #~ print c3,'can not be extended'
    #~ Im123 = []
    #~ for im1 in Im1:
        #~ for im2 in Im2:
            #~ for im3 in Im3:
                #~ print im1.name(), im2.name(), im3.name()
                #~ if X.potential_partial_isomorphism([im1, im2, im3] + [0]*6):
                    #~ Im123.append((im1,im2,im3))
                #~ else:
                    #~ print "no extension"
    #~ print
    #~ print "FIRST THREE VARS:",len(Im123),"POSSIBILITIES"
    #~ print
