/* vim: set syntax=magma : */
/*
*/

    SetColumns(0);
    //SetAssertions(2);

    AttachSpec("~/AbVarFq/spec");
    //AttachSpec("~/AlgEt/spec"); // this spec file in is magma since 2.29
    AttachSpec("~/AlgEt/specMod");
    AttachSpec("~/AlgEt/specMtrx");
    AttachSpec("~/IsomClAbVarFqCommEndAlg/spec");

//    SetVerbose("alpha_at_precision",2);
//    SetVerbose("DieudonneModules",2);
//    SetVerbose("Algorithm_2",2);
//    SetVerbose("Algorithm_3",2);

    PP<x>:=PolynomialRing(Integers());

    h:=x^8+x^7+x^6+4*x^5-4*x^4+16*x^3+16*x^2+64*x + 256;
    assert IsSquarefree(h);
    isog:=IsogenyClass(h);
    g:=Dimension(isog);
    q:=FiniteField(isog);
    t,p,a:=IsPrimePower(q); assert t;

    t0:=Cputime();
    iso:=IsomorphismClasses(isog);
    t1:=Truncate(Cputime(t0)) div 60;
    printf "We got %o isomorphism classes in %o minutes\n",#iso,t1;

    R:=ZFVOrder(isog);
    m0,J,dJ,Q,mQ,F,V:=SemilinearOperators(isog);
    E:=Algebra(R);

    oo:=OverOrders(R);
    OE:=MaximalOrder(E);
    _,P,_:=PrimesOfZFVAbove_p(isog);
    assert #P eq 1;
    P:=P[1];
    // P is the local-local maximal ideal of R above p

    is_maximal_at_01:=function(S)
    // check if the overorder S of R is maximal locally at its local-local part.
        return S!!OneIdeal(OE) eq OneIdeal(S) + S!!OE!!P;
    end function;

    Ep,mEp:=TotallyRealSubAlgebra(E);
    OEp:=MaximalOrder(Ep);
    "p is " cat (#PlacesAboveRationalPrime(Ep,p) eq g select "" else "not ") cat "totally split in E^+";
    OEp:=[mEp(z):z in ZBasis(OEp)];
    contains_OEp:=func< S | forall{z:z in OEp|z in S}>;


    ind:=[Index(OE,S):S in oo];
    ParallelSort(~ind,~oo);
    Reverse(~oo);
    ends:=[ EndomorphismRing(A) : A in iso ];
    printf "For each overorder S, we print the following string of data:\n\tiS = which overorder of Z[pi,q/pi]\n\t[OE:S]\n\td(S) = #Dieudonné modules with End S\n\th(S)=#Pic(S)\n\ta numbers of the DM with End S\n\tis S maximal at (0,1)?\n\tdoes S contain O_{E^+}?\n\tindices of minimal overorders\n\n";
    for iS->S in oo do
        dmS:={@ dmA where _,dmA:=IsomDataCommEndAlg(A) : A in iso | EndomorphismRing(A) eq S @};
        // a-numbers
        a_nums:=[];
        for dm in dmS do
            assert dm subset J;
            M:=sub<Q|[mQ(z):z in ZBasis(dm)]>;
            FM:=sub<M|[M!F(M.i):i in [1..Ngens(M)]]>;
            VM:=sub<M|[M!V(M.i):i in [1..Ngens(M)]]>;
            Append(~a_nums,Ilog(q,Index(M,FM+VM)));
        end for;
        // indices of minimal overorders (to find the place of S in the graph of inclusions)
        ind_min_oo:=[ Index(oo,T) : T in MinimalOverOrders(S) ];
        printf "%o,%o,%o,%o,%o,%o,%o,%o\n",iS,Index(OE,S),#dmS,#PicardGroup(S),a_nums,is_maximal_at_01(S),contains_OEp(S),ind_min_oo;
    end for;

/*

*/

























