## List of instrinsics in ./CreationAbVarFq.m:

> <pre><b>IsomDataCommEndAlg</b>(A::AbelianVarietyFq)->AlgEtQIdl,AlgEtQIdl,AlgEtQIdl,AlgEtQOrd</pre>
<em>Given an abelian variety over Fq with commutative Fq-endomorphism algebra, returns the tuple <I,M,S,L> as defined in AbelianVarietyCommEndAlg.</em>

> <pre><b>AbelianVarietyCommEndAlg</b>(isog::IsogenyClassFq,tup:Tup)->AbelianVarietyFq</pre>
<em>Given an isogeny class of abelian varieties over Fq with commutative Fq-endomorphism algebra, i.e. whose Weil polynomial is squarefree, and tuple <I,M,L,S> where
- I is a fractional ideal over the ZFVOrder of isog;
- M is a WR\{F,V\</em>


## List of instrinsics in ./PrimesIsog.m:

> <pre><b>SingPrimesOfZFVAwayFrom_p</b>(isog:IsogenyClassFq)->SeqEnum[AlgEtQIdl]</pre>
<em>Returns the singular maximal ideals of the ZFVOrder of isog which do not contian p.</em>

> <pre><b>PlacesOfQFAbove_p</b>(isog:IsogenyClassFq)->SeqEnum[AlgEtQIdl],SeqEnum[AlgEtQIdl],SeqEnum[AlgEtQIdl]</pre>
<em>Returns a triple of sequences containing the maximal ideals with slope equal to 0, in (0,1), equal to 1, respectively</em>

> <pre><b>PrimesOfZFVAbove_p</b>(isog:IsogenyClassFq)->SeqEnum[AlgEtQIdl],SeqEnum[AlgEtQIdl],SeqEnum[AlgEtQIdl]</pre>
<em>Returns 3 sequences of maximal ideals of the ZFVOrder of isog consisting, respectively, of the maximal ideals of slope 0, slope in the open interval (0,1) and slope 1, where here with slope of P we mean the slope of any maximal ideal of the maximal order containing P.</em>

> <pre><b>Slope</b>(P::AlgEtQIdl : CheckMaximal:=true)->FldRatElt</pre>
<em>Given a maximal ideal P of the maximal order of the commutative endomorphism algebra E=Q[pi] of abelian varieties over Fq, with q=p^a, it returns the slope of P, which is defined as val_P(pi)/(a\*e_P) where val_P(pi) is the valuation of pi at P and e_P is the ramification index of P.
If the vararg CheckMaximal is set to false, the instrinsic will accept as input also a P is a maximal ideal of a non-maximal order and return val_PP(pi)/(a\*e_PP) where PP is a maximal ideal of the maximal order above P. If the output is not 0 or 1, then it is not well defined: it will be a rational number in the open interval (0,1), but the exact value might depend on the choice of PP above P.</em>


## List of instrinsics in ./DieudonneModules.m:

> <pre><b>DieudonneAlgebraCommEndAlg</b>(isog::IsogenyClassFq)->FldNum,RngOrd,RngOrdIdl,RngIntElt,AlgEtQ,AlgEtQElt,AlgEtQOrd,Map,UserProgram,UserProgram,UserProgram</pre>
<em>Let isog be an isogeny class of abelian varieties over Fq, with q=p^a, with commutative endomorphism algebra E=Q[pi]. This intrisic populates the attribute DiedudonneAlgebraCommEndAlg of the isogeny class, which consists of the tuple <L,OL,PL,normPL,A,pi_A,OA,Delta_map,WR,Delta_inverse_ideal,primes_of_A_above_place_of_E,primes_of_S_of_slope_in_01,alpha_at_precision> where: 
- L is a number field such that L\otimes_Q Qp is an unramified field extension of Qp of degree a; OL is its maximal order and PL=p\*OL; normPL is the size of OL/PL;
- A is an etale algebra isomorphic to E\otimes_Q L; OA is its maximal order;
- WR is an order in A, isomorphic to R\otimes_Z OA.
- Delta_map is the natural embedding of E->A; pi_A is the image of pi, the Frobenius endomorphism of isog;
- Delta_inverse_ideal is a function that given a fractional WR ideal returns its preimage via Delta_map;
- primes_of_A_above_place_of_E is a function that given A and a maximal ideal P of E returns the maximal ideals of OA above P;
- primes_of_S_of_slope_in_01 is a function that an overorder S of WR returns its maximal ideals P with 'slope' in the open interval (0,1), that is, P's that are below the maximal ideals of OA, which are above maximal ideals of OE of slope in (0,1); 
- alpha_at_precision is a function that given a positive integer m returns an element alpha of OA, as reqired by Algorithm 3 of the paper to define the reductions of the semilinear operator F with the Frobenius property and of W-type; more precisely: alpha is congruent mod p^m\*OA to an element alpha' whose image in A\otimes_Q Qp = \prod_nu \prod_(i=1)^gnu LE_nu has nu component alpha'_nu=(1,....,1,u) where N_(LE_nu/E_nu)(u)=pi_nu.</em>

> <pre><b>SemilinearOperators</b>(isog::IsogenyClassFq)->RngIntElt,AlgEtQIdl,AlgEtQIdl,GrpAb,Map,Map,Map</pre>
<em>Returns the homonymous attribute of the isogeny class, which constist of the following informations: m0,J,den_ideal,Qm0,qm0,FQm0,VQm0, where (see DieudonneAlgebraCommEndAlg for the missing definitions):
- m0 is a positive integer;
- J is a WR-ideal with maximal endomorphism ring OA which is stable under the action of F and V=pF^-1, for some semilinear operator F with the Frobenius property of and of W-type;
- den_ideal = p^m0\*J+P01^M\*J, where P01 is the product of the maximal ideals of WR which are above the unique local-local maximal ideal of R, and M is chosen so that P01^MJ c J locally at every such maximal ideal;
- Qm0 is the abelian group J/den_ideal and qm0 is the quotient map J->Qm0;
- FQm0 and Vm0 are additive maps induced by semilinear operators F and V as above. They represent the Frobenius and Verschiebung acting on Dieudonne modules.
The attribute SemilinearOperators needs to be computed beforehand, during a run of IsomorphismClassesDieudonneModulesCommEndAlg. During this run, the integer m0 is automatically computed by the program to guarantee that every fractional W'R-ideal I' whose extension to OA is F and V stable ideal J and den_ideal c I'. These two conditions allow us to verify if I' is a W'R\{F,V\</em>

> <pre><b>;


////////////////////////////////////////////////////////////////////////////////////
//////////////////////// IsomorphismClassesDieudonneModules ////////////////////////
////////////////////////////////////////////////////////////////////////////////////

intrinsic IsomorphismClassesDieudonneModulesCommEndAlg</b>(isog::IsogenyClassFq : IncreaseMinimumPrecisionForSemilinearFVBy:=0)->SeqEnum[AlgEtQIdl]</pre>
<em>Given an isogeny class of abelian varieties over Fq with commutative endomorphism algebra returns representatives of the isomorphism classes of th local-local parts of the Dieudonné modules of the varieteis. These representatives are given as fractional WR-ideals, where WR is defined as in DiedudonneAlgebraCommEndAlg, which are stable under the action of semilinar operators F and V=pF^-1, where F has the Frobenius property and is of W-type. See the paper for the definitions. The action of F and V is computed on a quotient, whose size is determined by a precision parameter m. This m is calculated automatically to guarantee that the output of this function is correct. One can increase this parameter by setting the VarArg IncreaseMinimumPrecisionForSemilinearFVBy to a strinctly positive value. The operators can be recovered using SemilinearOperators.</em>


## List of instrinsics in ./CreationAbVarFq.m:

> <pre><b>IsomDataCommEndAlg</b>(A::AbelianVarietyFq)->AlgEtQIdl,AlgEtQIdl,AlgEtQIdl,AlgEtQOrd</pre>
<em>Given an abelian variety over Fq with commutative Fq-endomorphism algebra, returns the tuple <I,M,S,L> as defined in AbelianVarietyCommEndAlg.</em>

> <pre><b>AbelianVarietyCommEndAlg</b>(isog::IsogenyClassFq,tup:Tup)->AbelianVarietyFq</pre>
<em>Given an isogeny class of abelian varieties over Fq with commutative Fq-endomorphism algebra, i.e. whose Weil polynomial is squarefree, and tuple <I,M,L,S> where
- I is a fractional ideal over the ZFVOrder of isog;
- M is a WR\{F,V\</em>


## List of instrinsics in ./PrimesIsog.m:

> <pre><b>SingPrimesOfZFVAwayFrom_p</b>(isog:IsogenyClassFq)->SeqEnum[AlgEtQIdl]</pre>
<em>Returns the singular maximal ideals of the ZFVOrder of isog which do not contian p.</em>

> <pre><b>PlacesOfQFAbove_p</b>(isog:IsogenyClassFq)->SeqEnum[AlgEtQIdl],SeqEnum[AlgEtQIdl],SeqEnum[AlgEtQIdl]</pre>
<em>Returns a triple of sequences containing the maximal ideals with slope equal to 0, in (0,1), equal to 1, respectively</em>

> <pre><b>PrimesOfZFVAbove_p</b>(isog:IsogenyClassFq)->SeqEnum[AlgEtQIdl],SeqEnum[AlgEtQIdl],SeqEnum[AlgEtQIdl]</pre>
<em>Returns 3 sequences of maximal ideals of the ZFVOrder of isog consisting, respectively, of the maximal ideals of slope 0, slope in the open interval (0,1) and slope 1, where here with slope of P we mean the slope of any maximal ideal of the maximal order containing P.</em>

> <pre><b>Slope</b>(P::AlgEtQIdl : CheckMaximal:=true)->FldRatElt</pre>
<em>Given a maximal ideal P of the maximal order of the commutative endomorphism algebra E=Q[pi] of abelian varieties over Fq, with q=p^a, it returns the slope of P, which is defined as val_P(pi)/(a\*e_P) where val_P(pi) is the valuation of pi at P and e_P is the ramification index of P.
If the vararg CheckMaximal is set to false, the instrinsic will accept as input also a P is a maximal ideal of a non-maximal order and return val_PP(pi)/(a\*e_PP) where PP is a maximal ideal of the maximal order above P. If the output is not 0 or 1, then it is not well defined: it will be a rational number in the open interval (0,1), but the exact value might depend on the choice of PP above P.</em>


## List of instrinsics in ./DieudonneModules.m:

> <pre><b>DieudonneAlgebraCommEndAlg</b>(isog::IsogenyClassFq)->FldNum,RngOrd,RngOrdIdl,RngIntElt,AlgEtQ,AlgEtQElt,AlgEtQOrd,Map,UserProgram,UserProgram,UserProgram</pre>
<em>Let isog be an isogeny class of abelian varieties over Fq, with q=p^a, with commutative endomorphism algebra E=Q[pi]. This intrisic populates the attribute DiedudonneAlgebraCommEndAlg of the isogeny class, which consists of the tuple <L,OL,PL,normPL,A,pi_A,OA,Delta_map,WR,Delta_inverse_ideal,primes_of_A_above_place_of_E,primes_of_S_of_slope_in_01,alpha_at_precision> where: 
- L is a number field such that L\otimes_Q Qp is an unramified field extension of Qp of degree a; OL is its maximal order and PL=p\*OL; normPL is the size of OL/PL;
- A is an etale algebra isomorphic to E\otimes_Q L; OA is its maximal order;
- WR is an order in A, isomorphic to R\otimes_Z OA.
- Delta_map is the natural embedding of E->A; pi_A is the image of pi, the Frobenius endomorphism of isog;
- Delta_inverse_ideal is a function that given a fractional WR ideal returns its preimage via Delta_map;
- primes_of_A_above_place_of_E is a function that given A and a maximal ideal P of E returns the maximal ideals of OA above P;
- primes_of_S_of_slope_in_01 is a function that an overorder S of WR returns its maximal ideals P with 'slope' in the open interval (0,1), that is, P's that are below the maximal ideals of OA, which are above maximal ideals of OE of slope in (0,1); 
- alpha_at_precision is a function that given a positive integer m returns an element alpha of OA, as reqired by Algorithm 3 of the paper to define the reductions of the semilinear operator F with the Frobenius property and of W-type; more precisely: alpha is congruent mod p^m\*OA to an element alpha' whose image in A\otimes_Q Qp = \prod_nu \prod_(i=1)^gnu LE_nu has nu component alpha'_nu=(1,....,1,u) where N_(LE_nu/E_nu)(u)=pi_nu.</em>

> <pre><b>SemilinearOperators</b>(isog::IsogenyClassFq)->RngIntElt,AlgEtQIdl,AlgEtQIdl,GrpAb,Map,Map,Map</pre>
<em>Returns the homonymous attribute of the isogeny class, which constist of the following informations: m0,J,den_ideal,Qm0,qm0,FQm0,VQm0, where (see DieudonneAlgebraCommEndAlg for the missing definitions):
- m0 is a positive integer;
- J is a WR-ideal with maximal endomorphism ring OA which is stable under the action of F and V=pF^-1, for some semilinear operator F with the Frobenius property of and of W-type;
- den_ideal = p^m0\*J+P01^M\*J, where P01 is the product of the maximal ideals of WR which are above the unique local-local maximal ideal of R, and M is chosen so that P01^MJ c J locally at every such maximal ideal;
- Qm0 is the abelian group J/den_ideal and qm0 is the quotient map J->Qm0;
- FQm0 and Vm0 are additive maps induced by semilinear operators F and V as above. They represent the Frobenius and Verschiebung acting on Dieudonne modules.
The attribute SemilinearOperators needs to be computed beforehand, during a run of IsomorphismClassesDieudonneModulesCommEndAlg. During this run, the integer m0 is automatically computed by the program to guarantee that every fractional W'R-ideal I' whose extension to OA is F and V stable ideal J and den_ideal c I'. These two conditions allow us to verify if I' is a W'R\{F,V\</em>

> <pre><b>;


////////////////////////////////////////////////////////////////////////////////////
//////////////////////// IsomorphismClassesDieudonneModules ////////////////////////
////////////////////////////////////////////////////////////////////////////////////

intrinsic IsomorphismClassesDieudonneModulesCommEndAlg</b>(isog::IsogenyClassFq : IncreaseMinimumPrecisionForSemilinearFVBy:=0)->SeqEnum[AlgEtQIdl]</pre>
<em>Given an isogeny class of abelian varieties over Fq with commutative endomorphism algebra returns representatives of the isomorphism classes of th local-local parts of the Dieudonné modules of the varieteis. These representatives are given as fractional WR-ideals, where WR is defined as in DiedudonneAlgebraCommEndAlg, which are stable under the action of semilinar operators F and V=pF^-1, where F has the Frobenius property and is of W-type. See the paper for the definitions. The action of F and V is computed on a quotient, whose size is determined by a precision parameter m. This m is calculated automatically to guarantee that the output of this function is correct. One can increase this parameter by setting the VarArg IncreaseMinimumPrecisionForSemilinearFVBy to a strinctly positive value. The operators can be recovered using SemilinearOperators.</em>


## List of instrinsics in ./IsomorphismClasses.m:

> <pre><b>IsomorphismClassesAwayFromLocalLocalCommEndAlg</b>(isog::IsogenyClassFq)->SeqEnum[AlgEtQIdl]</pre>
<em>Returns a sequence of fractional ZFVOrder-ideals representing the local isomorphism classes for all primes different from the characteristic p, the local-étale part and the étale-local part of the ZFVOrder of isog.</em>

> <pre><b>IsomorphismClassesCommEndAlg</b>(isog::IsogenyClassFq : IncreaseMinimumPrecisionForSemilinearFVBy:=0)->SeqEnum[AbVarFq]</pre>
<em>Given an isogeny class of abelian varieties over a finite field Fq, it returns representatives of the Fq-isomorphism classes in the isogeny class. The meaning of the VarArg IncreaseMinimumPrecisionForSemilinearFVBy is given in the description of IsomorphismClassesDieudonneModulesCommEndAlg.</em>


## List of instrinsics in ./SaveLoad.m:

> <pre><b>SaveAbVarFqCommEndAlg</b>(classes::SeqEnum[AbelianVarietyFq])->MonStgElt</pre>
<em>Given a sequence of abelian vareities belonging to an isogney class over Fq with commutative Fq-endomorphism algebra, returns a string containing all the info about the isomorphism classes of the varietis. This string can be loaded using LoadAbVarFqCommEndAlg defined below.</em>

> <pre><b>LoadAbVarFqCommEndAlg</b>(isog::IsogenyClassFq,input::MonStgElt)->SeqEnum[AbelianVarietyFq]</pre>
<em>Given an isogeny class of abelian varieties over Fq with commutative Fq-endomorphism algebra and the string produced by SaveAbVarFqCommEndAlg, returns the sequence of abelian varieties which is stored in the string. The SemilinearOperator attribute of isog is populated (see SemilinearOperators for details).</em>


