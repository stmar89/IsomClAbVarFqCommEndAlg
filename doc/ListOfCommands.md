## List of instrinsics in ./UnitsQuotients.m:

> <pre><b>UnitGroupQuotientAtSlope</b>(isog::IsogenyClassFq,S::AlgEtQOrd,slopes::MonStgElt)->GrpAb,Map,AlgEtQIdl</pre>
<em>Given an isogeny class isog, an order S in the DieudonneAlgebra and string variable slopes with values "0","(0,1)","1" or "all", returns the triple U,u,I where U=OA'^\*/S'^\*, where ' denotes the 0,(0,1),1 or p-part, the map u:U->OA 
together with an ideal I of OA such that OA'/S' = (OA/I)/(S/I).</em>

> <pre><b>UnitGroupQuotientAtSlopeFixedBySigma</b>(isog::IsogenyClassFq,S::AlgEtQOrd,slopes::MonStgElt)->GrpAb,Map,SeqEnum[AlgEtQElt]</pre>
<em>Given an isogeny class isog, an order S in the DieudonneAlgebra and string variable slopes with values "0","(0,1)","1" or "all", returns the triple U,u where U=OA'^\*/S'^\*Delta(OE'^\*), where ' denotes the 0,(0,1),1 or p-part, the map u:U->OA together a list of representatives in OA of U.</em>


## List of instrinsics in ./CRT_expansion.m:

> <pre><b>ChineseRemainderTheoremFunctions</b>(J::AlgEtQIdl,Is::SeqEnum[AlgEtQIdl])-> Map,Map</pre>
<em>Given a fractional S-ideal J and sequence Is of N integral fractional S-ideals I_1,\ldots,I_N, pairwise coprime, returns a map J \to J^N representing the natural isomorphism J/I\*J \to J/I_1\*J x ... x J/I_N\*J, where I=\prod_i I_i, and a map J^N \to J representing the inverse.</em>

> <pre><b>LocalGenerators</b>(J::AlgEtQIdl,P::AlgEtQIdl)->SeqEnum[AlgEtQElt]</pre>
<em>Given a fractional R-ideal J and a maximal ideal P of R, returns a sequence of elements of J that generates the localization of J at P.</em>

> <pre><b>LocalGenerators</b>(J::AlgEtQIdl,Ps::SeqEnum[AlgEtQIdl])->SeqEnum[AlgEtQElt]</pre>
<em>Given a fractional R-ideal J and a sequence Ps of maximal ideal P of R, returns a sequence of elements of J that generates the localization of J at each P in Ps.</em>


## List of instrinsics in ./CreationAbVarFq.m:

> <pre><b>IsomDataCommEndAlg</b>(A::AbelianVarietyFq)->AlgEtQIdl,AlgEtQIdl,AlgEtQIdl,AlgEtQOrd</pre>
<em>Given an abelian variety over Fq with commutative Fq-endomorphism algebra, returns the tuple <I,M,L,S,slope> as defined in AbelianVarietyCommEndAlg.</em>

> <pre><b>AbelianVarietyCommEndAlg</b>(isog::IsogenyClassFq,tup:Tup)->AbelianVarietyFq</pre>
<em>Given an isogeny class of abelian varieties over Fq with commutative Fq-endomorphism algebra, i.e. whose Weil polynomial is squarefree, and a tuple <I,M,L,S,slope> where
- I is a fractional ideal over the ZFVOrder of isog;
- M is a WR\{F,V\}-ideal (see DieudonneAlgebraCommEndAlg for definitions);
- S in an overorder of the ZFVOrder;
- L is an invertible fractional S-ideal;
- slope is either "(0,1)" or "all" depending on which method was used;
returns the unique abelian variety in isog with EndomorphismRing S such that: the l-Tate modules are isomorphic to I (for all l neq p), if slope is "(0,1)" also the étale-local and local-étale part of the Dieudonné module are determined by I, while the local-local part is determined by M, while if slope is "all" then the Dieudonné module is only determined by M; L determines its position in the orbit of the class group of S acting on the local information just described.</em>


## List of instrinsics in ./PrimesIsog.m:

> <pre><b>SingPrimesOfZFVAwayFrom_p</b>(isog:IsogenyClassFq)->SeqEnum[AlgEtQIdl]</pre>
<em>Returns the singular maximal ideals of the ZFVOrder of isog which do not contian p.</em>

> <pre><b>PrimesOfZFVAbove_p</b>(isog:IsogenyClassFq)->SeqEnum[AlgEtQIdl],SeqEnum[AlgEtQIdl],SeqEnum[AlgEtQIdl]</pre>
<em>Returns 3 sequences of maximal ideals of the ZFVOrder of isog consisting, respectively, of the maximal ideals of slope 0, slope in the open interval (0,1) and slope 1, where here with slope of P we mean the slope of any maximal ideal of the maximal order containing P.</em>

> <pre><b>PlacesOfQFAbove_p</b>(isog:IsogenyClassFq)->SeqEnum[AlgEtQIdl],SeqEnum[AlgEtQIdl],SeqEnum[AlgEtQIdl]</pre>
<em>Returns a triple of sequences containing the maximal ideals with slope equal to 0, in (0,1), equal to 1, respectively</em>

> <pre><b>UniformizersInQFAt_p</b>(isog::IsogenyClassFq,nus::SeqEnum[AlgEtQIdl])->SeqEnum[AlgEtQElt]</pre>
<em>Given an isogeny class isog and a sequence of places nus of the DeligneAlgebra, returns a sequence of uniformizers t_nu of each place nu in nus such that t_nu is a unit modulo every other place above p.</em>

> <pre><b>PlacesOfDieudonneAlgebraAbovePlaceOfQF</b>(isog::IsogenyClassFq,nu::AlgEtQIdl)->SeqEnum[AlgEtQIdl]</pre>
<em>Returns the places of the DieudonneAlgebra of isog above a the given place nu of the DeligneAlgebra.</em>

> <pre><b>PlacesOfDieudonneAlgebraSortedBySigmaAbovePlaceOfQF</b>(isog::IsogenyClassFq,nu::AlgEtQIdl)->SeqEnum[AlgEtQIdl]</pre>
<em>Returns the places of the DieudonneAlgebra of isog above a the given place nu of the DeligneAlgebra, sorted by the action of the Frobenius automorphism sigma.</em>

> <pre><b>PrimesOfSAbove_p</b>(isog::IsogenyClassFq,S::AlgEtQOrd)->SeqEnum[AlgEtQIdl],SeqEnum[AlgEtQIdl],SeqEnum[AlgEtQIdl]</pre>
<em>Given an order S in the DieudonneAlgebra of the isogeny class isog over a finite field of charateristic p returns three sequences consisting of the pries of S above p of slope equal to 0, in (0,1), equalt to 1, respetively.</em>

> <pre><b>Slope</b>(P::AlgEtQIdl : CheckMaximal:=true)->FldRatElt</pre>
<em>Given a maximal ideal P of the maximal order of the commutative endomorphism algebra E=Q[pi] of abelian varieties over Fq, with q=p^a, it returns the slope of P, which is defined as val_P(pi)/(a\*e_P) where val_P(pi) is the valuation of pi at P and e_P is the ramification index of P.
If the vararg CheckMaximal is set to false, the instrinsic will accept as input also a P is a maximal ideal of a non-maximal order and return val_PP(pi)/(a\*e_PP) where PP is a maximal ideal of the maximal order above P. If the output is not 0 or 1, then it is not well defined: it will be a rational number in the open interval (0,1), but the exact value might depend on the choice of PP above P.</em>


## List of instrinsics in ./DieudonneModules.m:

> <pre><b>DieudonneAlgebraCommEndAlg</b>(isog::IsogenyClassFq)->FldNum,RngOrd,RngOrdIdl,RngIntElt,AlgEtQ,AlgEtQElt,AlgEtQOrd,Map,AlgEtQOrd,Tup,Tup</pre>
<em>Let isog be an isogeny class of abelian varieties over Fq, with q=p^a, with commutative endomorphism algebra E=Q[pi]. This intrisic populates the attribute DiedudonneAlgebraCommEndAlg of the isogeny class, which consists of the tuple 
<L,OL,PL,normPL,A,pi_A,OA,Delta_map,WR,A_as_vector_space_over_L_data,OA_as_abelian_group_data> where
- L is a number field such that L\otimes_Q Qp is an unramified field extension of Qp of degree a; OL is its maximal order and PL=p\*OL; normPL is the size of OL/PL;
- A is an etale algebra isomorphic to E\otimes_Q L; OA is its maximal order;
- WR is an order in A, isomorphic to R\otimes_Z OE locally at p and equal to OA everywhere else.
- Delta_map is the natural embedding of E->A; pi_A is the image of pi, the Frobenius endomorphism of isog;
- A_as_vector_space_over_L_data is a tuple consistsing of four L-linear isomorphisms m1,m2,m3,m4 allowing to represent A as an L-vector space. Let V1 be the direct sums of L[x]/(gi) where gi runs over the factors of the Weil polynomial over L[x] and where each extension of L is considered as an L-vector space using the power basis. Let V2 be L-vector space structure on A induced by the L-basis pi_A^i where i=0,..,dim_Q(E). Then m1:A->V1 and m2:V2->V1 are the natural isomorphisms and m3:A->V2 is the composition a:->m2^-1(m1(a)). In other words, it corresponds to the presentation A=L[pi_A] of A, or equivalently A = Z[pi] \otimes_Z L. Finally, m4:A->V2 is an L-isomorphism in which we instead use the ZBasis of OE; it corresponds to the decomposition A = OE \otimes_Z L.
- OA_as_abelian_group_data is the tuple <FOA,fOA,imageDeltaOE_inFOA> where FOA is a free abelian group and fOA:=OA->FOA is an isomorphism, and imageDeltaOE_inFOA is the image of Delta(OE) in FOA. This tuple is used to compute Delta^-1 of orders and ideals in the DieudonneAlgebra.</em>


## List of instrinsics in ./Sigma.m:

> <pre><b>SigmaOnQuotientOfOA</b>(isog::IsogenyClassFq,I::AlgEtQIdl)->GrpAb,Map,Map</pre>
<em>Given an isogeny class isog and a fractional OA-ideal I of the maximal order OA of the DieudonneAlgebra A=L otims Eof isog, returns Q,mQ,sigma_Q where Q=OA/I, mQ:OA->Q and sigma_Q is the homorphism induced by the Frobenius automorphism of L. The output is cached in an attribute populated on demand.</em>


## List of instrinsics in ./DeltaIdeals.m:

> <pre><b>DeltaIdeal</b>(isog::IsogenyClassFq, I::AlgEtQIdl)->AlgEtQIdl</pre>
<em>Given a fractional Z[pi,q/pi]-ideal I in the DeligneAlgebra of isog, returns the WR-ideal Delta(I) in the DiudonneAlgebra.</em>

> <pre><b>DeltaInverseIdeal</b>(isog::IsogenyClassFq, I::AlgEtQIdl)->AlgEtQIdl</pre>
<em>Given a fractional WR-ideal I in the DieudonneAlgebra of isog, returns Delta^-1(I), which is a Z[pi,q/pi]-ideal in the DeligneAlgebra.</em>

> <pre><b>DeltaInverseIdealpPart</b>(isog::IsogenyClassFq, I::AlgEtQIdl)->AlgEtQIdl</pre>
<em>Given a fractional WR-ideal I in the DieudonneAlgebra of isog, returns a Z[pi,q/pi]-ideal J in the DeligneAlgebra such that J_p = Delta^-1(I_p).</em>

> <pre><b>DeltaScaleInside</b>(isog::IsogenyClassFq,J::AlgEtQIdl,Is::SeqEnum[AlgEtQIdl])->SeqEnum[AlgEtQIdl],RngIntElt</pre>
<em>Given an isogeny class isog, a fractional WR-ideal J and a sequence of fractional WR-ideals Is of the DieudonneAlgebra it returns a sequence IIs and an integer m0 such that, for each i: Is[i] is Delta-isomorphic to IIs[i], each IIs[i] is inside J, and m0=Max(Valuation(p,Index(J,IIs[i])) is small.</em>


## List of instrinsics in ./SemilinearOperators.m:

> <pre><b>AlphaWTypeAtPlace</b>(isog::IsogenyClassFq,nu::AlgEtQIdl,m::RngIntElt)->AlgEtQElt,AlgEtQIdl</pre>
<em>Given an isogeny class isog, a place nu of the DeligneAlgebra and a positive integer m, returns an integral element alpha of the DieudonneAlgebra A whose image in the quotient (OA/p^mOA)_nu is congruent to the nu-component alpha_nu of an element of of W-type, that is, such that alpha'_nu=(1,....,1,u) where N_(LE_nu/E_nu)(u)=pi_nu. Moreover, it returns also the product of maximal ideals of A above nu, raised to the power m\*e where e is the common ramification index.</em>

> <pre><b>we attempt to copute F and V on Qm0 and Qm0_1 by splitting the computation over 
// the places of OE of slope in</b>(0,1) and then taking a CRT-direct sum of the local homomorphisms.</pre>
<em>Given an isogeny class isog, an ideal J over the maximal order of the DieudonneAlgebra which is F-V-stable for F,V of W-type, a place nu of the DeligneAlgebra and a precision m0, returns Q,q,FQ,VQ where Q is isomorphic to (J/p^m0\*J)_nu, q:J->Q is the natural projection and FQ,VQ are the reductions of F,V to Q.</em>

> <pre><b>SemilinearOperatorsWType</b>(isog::IsogenyClassFq,J::AlgEtQIdl,nus::SeqEnum[AlgEtQIdl],m0::RngIntElt)->GrpAb,Map,Map,Map</pre>
<em>Given an isogeny class isog, an ideal J over the maximal order of the DieudonneAlgebra which is F-V-stable for F,V of W-type, a sequence of places nus of the DeligneAlgebra and a precision m0, returns Q,q,FQ,VQ where Q is isomorphic to direct sum of (J/p^m0\*J)_nu for nu in nus, q:J->Q is the natural projection and FQ,VQ are the reductions of F,V to Q.</em>

> <pre><b>SemilinearOperatorsWType</b>(isog::IsogenyClassFq,J::AlgEtQIdl,m0::RngIntElt,slopes::MonStgElt)->GrpAb,Map,Map,Map,AlgEtQIdl,RngIntElt,AlgEtQIdl</pre>
<em>Given an isogeny class isog, an ideal J over the maximal order of the DieudonneAlgebra which is F-V-stable for F,V of W-type, and a precision m0, returns Q,q,FQ,VQ where Q is isomorphic to direct sum of (J/p^m0\*J)_nu for nu of slope in (0,1) or any --depending whether the argument slope is "(0,1)" or "all"-- q:J->Q is the natural projection and FQ,VQ are the reductions of F,V to Q. Moreover the intrinsic returns also the ideal den_ideal so that Q=J/den_ideal, and m0 and J.</em>

> <pre><b>SemilinearOperators</b>(isog::IsogenyClassFq)->GrpAb,Map,Map,Map,AlgEtQIdl,RngIntElt,AlgEtQIdl,MonStgElt</pre>
<em>Returns the attribute SemilinearOperatorsWType of the isogeny class.</em>


## List of instrinsics in ./IsomorphismClassesDieudonneModulesCommEndAlg.m:

> <pre><b>ExponentsWTypeAtPlace</b>(isog::IsogenyClassFq,nu::AlgEtQIdl)->SeqEnum[SeqEnum[RngIntElt]]</pre>
<em>Given an isogeny class isog and a place nu of the Deligne Algebra, one can represent the isomorphism classes of Dieudonne Modules with maximal endomorphism rings as OA\{F,V\}-ideal in the DieudonneAlgebra A. These ideals can be efficiently described as vectors of powers of uniformizers. In particular, the property of being F-V-stable can be checked using the exponents of this power representation, assuming that the maximal ideal of A above nu are sorted according to the action of sigma. This intrinsic returns a sequence of the exponents, each one represented as a sequence of integers, describing the nu-components the isomorphism classes of WR\{F,V\}-ideals with maximal endomorphism OE.</em>

> <pre><b>ExponentsWType</b>(isog::IsogenyClassFq,slopes::MonStgElt)->SeqEnum[SeqEnum[RngIntElt]]</pre>
<em>Given an isogeny class isog and a place nu of the Deligne Algebra, one can represent the isomorphism classes of Dieudonne Modules with maximal endomorphism rings as OA\{F,V\}-ideal in the DieudonneAlgebra A. These ideals can be efficiently described as vectors of powers of uniformizers. In particular, the property of being F-V-stable can be checked using the exponents of this power representation, assuming that the maximal ideal of A above nu are sorted according to the action of sigma. This intrinsic returns a sequence of the exponents, each one represented as a sequence of integers, describing the isomorphism classes of WR\{F,V\}-ideals or WR'\{F',V'\}-ideals -- depending on whether slopes is "all" or "(0,1)" -- with maximal endomorphism OE.</em>

> <pre><b>WRIdealsWithFVStableExtensionToOA</b>(isog::IsogenyClassFq,slopes::MonStgElt)->SeqEnum[AlgEtQIld]</pre>
<em>Given an isogeny class isog, if slopes is "all" then returns a sequence of fraction WR-ideals I whose extension I\*OA to the maximal order OA of the DieudonneAlgebra A is stable by the action of F and V, modulo Delta-isomorphisms; if slopes is "(0,1)" then on the local-local part of the previously described output is returned.</em>

> <pre><b>IsomorphismClassesDieudonneModulesCommEndAlg</b>(isog::IsogenyClassFq,slopes::MonStgElt : IncreaseMinimumPrecisionForSemilinearFVBy:=0)->SeqEnum[AlgEtQIdl]</pre>
<em>Given an isogeny class of abelian varieties over Fq with commutative endomorphism algebra returns representatives of the isomorphism classes of the local-local parts of the Dieudonné modules of the varieties. These representatives are given as fractional WR-ideals, where WR is defined as in DiedudonneAlgebraCommEndAlg, which are stable under the action of semilinar operators F and V=pF^-1, where F has the Frobenius property and is of W-type. See the paper for the definitions. The action of F and V is computed on a quotient, whose size is determined by a precision parameter m. This m is calculated automatically to guarantee that the output of this function is correct. One can increase this parameter by setting the VarArg IncreaseMinimumPrecisionForSemilinearFVBy to a strinctly positive value. The operators can be recovered using SemilinearOperatorsWType. The second argument slopes can have values "(0,1)" or "all" and determined whether only the local-local part of the whole Dieudonne modules are computed.</em>


## List of instrinsics in ./IsomorphismClasses.m:

> <pre><b>IsomorphismClassesAwayFromLocalLocalCommEndAlg</b>(isog::IsogenyClassFq)->SeqEnum[AlgEtQIdl]</pre>
<em>Returns a sequence of fractional ZFVOrder-ideals representing the local isomorphism classes for all primes different from the characteristic p, the local-étale part and the étale-local part of the ZFVOrder of isog.</em>

> <pre><b>IsomorphismClassesAwayFrom_pCommEndAlg</b>(isog::IsogenyClassFq)->SeqEnum[AlgEtQIdl]</pre>
<em>Returns a sequence of fractional ZFVOrder-ideals representing the local isomorphism classes for all primes different from the characteristic p of the ZFVOrder of isog.</em>

> <pre><b>IsomorphismClassesCommEndAlg</b>(isog::IsogenyClassFq : slopesDieudonneModules:="(0,1)", IncreaseMinimumPrecisionForSemilinearFVBy:=0)->SeqEnum[AbVarFq]</pre>
<em>Given an isogeny class of abelian varieties over a finite field Fq, it returns representatives of the Fq-isomorphism classes in the isogeny class. The VarArg slopesDieudonneModules can be either "(0,1)" (default) or "all": in the first case only the local-local part of the isomorphism classes of DieudonneModules will be computed using WR'\{F',V'\}-ideals and the rest is deduced using ZFV-ideals; in the second case ZFV-ideals are used only to compute the local parts away from the characteristic p, while WR\{F,V\}-modules are used to compute Dieudonné modules. The meaning of the VarArg IncreaseMinimumPrecisionForSemilinearFVBy is given in the description of IsomorphismClassesDieudonneModulesCommEndAlg.</em>


## List of instrinsics in ./GenDeligneModules.m:

> <pre><b>GeneralizedDeligneModule</b>(AV:AbelianVarietyFq)->AlgEtQIdl,AlgEtQIdl</pre>
<em>Given an abelian variety AV, it returns a pair (I,M) where I is a fractional ideal over R=ZFVOrder and M is a fractional ideal over WR (defined in DieudonneAlgebraCommEndAlg) such that I \otimes Zp = Delta_map^-1(M\otimes Zp). The ideal I encodes local information at l\neq p, the étale-local and local-étale information about AV, while M encodes the Dieudonne module.</em>


## List of instrinsics in ./SaveLoad.m:

> <pre><b>SaveAbVarFqCommEndAlg</b>(classes::SeqEnum[AbelianVarietyFq])->MonStgElt</pre>
<em>Given a sequence of abelian vareities belonging to an isogney class over Fq with commutative Fq-endomorphism algebra, returns a string containing all the info about the isomorphism classes of the varietis. This string can be loaded using LoadAbVarFqCommEndAlg defined below.</em>

> <pre><b>LoadAbVarFqCommEndAlg</b>(isog::IsogenyClassFq,input::MonStgElt)->SeqEnum[AbelianVarietyFq]</pre>
<em>Given an isogeny class of abelian varieties over Fq with commutative Fq-endomorphism algebra and the string produced by SaveAbVarFqCommEndAlg, returns the sequence of abelian varieties which is stored in the string. The SemilinearOperator attribute of isog is populated (see SemilinearOperators for details).</em>


