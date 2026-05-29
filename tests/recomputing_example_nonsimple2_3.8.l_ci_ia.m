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

    h:=x^6 + 11*x^5 + 60*x^4 + 208*x^3 + 480*x^2 + 704*x + 512;
    assert IsSquarefree(h);

    for slopes in ["(0,1)","all"] do
        if assigned isog then
            delete isog; //for the second run
        end if;
        printf "-------------------------\n";

        isog:=IsogenyClass(h);
        g:=Dimension(isog);
        q:=FiniteField(isog);
        t,p,a:=IsPrimePower(q); assert t;
        t0:=Cputime();
        iso:=IsomorphismClassesCommEndAlg(isog:slopesDieudonneModules:=slopes);
        t1:=Round(Cputime(t0));
        printf "Using slopesDieudonneModules:=%o and SetAssertions(%o),\n\twe got %o isomorphism classes in %o mins %o secs\n",
                slopes,GetAssertions(),#iso,t1 div 60,t1 mod 60;
        t0:=Cputime();
        gen_del_mods:=[GeneralizedDeligneModule(A):A in iso];
        t1:=Round(Cputime(t0));
        printf "\tGeneralizedDeligneModules computed in %o mins %o secs\n",
                t1 div 60,t1 mod 60;
        nu0,nu01,nu1:=PlacesOfQFAbove_p(isog);
        nus:=nu0 cat nu01 cat nu1;
        data_nus:=[<Slope(nu),RamificationIndex(nu),GCD(a,InertiaDegree(nu))>:nu in nus];
        data_nus:=StripWhiteSpace(Sprint(data_nus));
        printf "\t<s_nu,e_nu,g_nu> = %o\n",data_nus;

        R:=ZFVOrder(isog);
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
        printf "\tp is %o totally split in E^+\n\n",(#PlacesAboveRationalPrime(Ep,p) eq g select "" else "not ");
        OEp:=[mEp(z):z in ZBasis(OEp)];
        contains_OEp:=func< S | forall{z:z in OEp|z in S}>;


        Q,mQ,F,V,_,_,J:=SemilinearOperators(isog);
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
            printf "\t%o,%o,%o,%o,%o,%o,%o,%o\n",iS,Index(OE,S),#dmS,#PicardGroup(S),a_nums,is_maximal_at_01(S),contains_OEp(S),ind_min_oo;
        end for;
    end for;


/*

*/

























