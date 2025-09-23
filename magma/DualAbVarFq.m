/* vim: set syntax=magma : */

// TODO add licence

declare attributes AbelianVarietyFq : DualAbVarFq;

//TODO thsis import is not nice..I should probaly store Delta_inverse_ppart in an attribute
import "/home/stmar/IsomClAbVarFqCommEndAlg/GenDeligneModules.m" : Delta_inverse_ppart;

intrinsic DualAbelianVarietyCommEndAlg(AV::AbelianVarietyFq)->AlgEtQIdl,AlgEtQIdl
{Given an abelian variety over Fq with commutative endomorphism algebra, returns the generalized deligne module of the dual variety.}
    if not assigned AV`DualAbVarFq then
        I,M:=GeneralizedDeligneModule(AV); //I don't think we need to work with the Generalized Deligne Module
        q:=FiniteField(AV);
        p:=CharacteristicFiniteField(AV);
        isog:=IsogenyClass(AV);

        // Now, we construct Mv which is defined as
        // Mv = { x in A : Tr_{A/L} (xM) subseteq W }.
        // In practice, given a pseudo W-basis of M
        //      M = a_1 z_1 + ... + a_n z_n, 
        // with z_i in A and a_i a fractional W-ideal in L,
        // we have that Mv has pseudo W-basis
        //      Mv = a_1^{-1} \bar{z_1}^* + ... + a_n^{-1} \bar{z_n}^*,
        // where z_1^*,...,z_n^* is the Tr_{A/L}-dual basis to z_1,...,z_n.
        // So, let's get the pseudo basis.
        L,_,PL,_,A,pi_A,_,_,WR,_,_,_,_,_,A_as_vector_space_over_L_data:=DieudonneAlgebraCommEndAlg(isog);
        mAD,mLdD,mALd:=Explode(A_as_vector_space_over_L_data);
        Ld:=Codomain(mALd);
        // - Ld and D are both L-vector spaces of dimension d:=dim_L(A).
        // - mAD is the L-linear isomorphism  that represents A as \prod_i L[x]/g_i where h=\prod_i g_i in L[x], 
        // that is, the i-th component L[x]/g_i is seen as an L-vector space using the power basis.
        // - Ld is the KSpace L^d.
        // - mLdD is the isomorphism Ld->D where the image of the canonial basis is given by 
        //   the images of the powers of pi in D.
        // - mALd = is the composition of mAD with mLdD^-1

        d:=Dimension(Ld);
        // We need to apply the CM involution which is defined to be bar on E, and identity on L.
        L_basis_ofA_bar:=[ (q/pi_A)^i : i in [0..d-1] ];
        bar_onLd:=iso<Ld->Ld|[mALd(b):b in L_basis_ofA_bar]>;
// TODO We get the right output over Fp and in the ordinary case, as well as in the almost ordinary case.
//      (We tested a few examples)
//      We believe that we are missing 'some sigma' in this construction....
//      Below there is a pretty random tentative, which does not work...
//
// sigma:=[ s : s in Automorphisms(L) | s(L.1) ne L.1 ][1];
// sigma_onLd:=map<Ld->Ld|x:->Ld![sigma(c):c in Eltseq(x)]>;
// //bar_onLd:=sigma_onLd*iso<Ld->Ld|[sigma_onLd(mALd(b)):b in L_basis_ofA_bar]>;
// bar_onLd:=sigma_onLd;

        // We convert M into a Lattice over W, since 
        // Once we compute the right Gram matrix, we can 
        L_basis_ofA:=[ pi_A^i : i in [0..d-1] ];
        TrAL:=map<A->L|x:->Trace(Matrix([mALd(x*b):b in L_basis_ofA]))>;
        zbM:=ZBasis(M);
        zbM_inLd:=[mALd(z):z in zbM];
        M_lat:=NumberFieldLattice(zbM_inLd);
        bM_lat:=Basis(M_lat); //over W
        assert M eq Ideal(WR,&cat[[(bb[i]*c)@@mALd:c in Basis(cc[i])] : i in [1..#bb]]) 
                where bb:=Basis(M_lat) where cc:=CoefficientIdeals(M_lat);
        bM_lat_inA:=[b@@mALd:b in bM_lat];
        Gram_M:=MatrixRing(L,d)![TrAL(x*y):x,y in bM_lat_inA];
// Gram_M:=MatrixRing(L,d)![TrAL(x*  sigma_onLd(y)@@mALd  ):x in bM_lat_inA, y in bM_lat];
        M_lat:=NumberFieldLattice(bM_lat : Gram:=Gram_M);
        Mv_lat:=Dual(M_lat);
        //TODO assert forall{i:i,j in [1..#Basis(M_lat)]| TrAL(Basis(M_lat)[i]
        ci:=CoefficientIdeals(Mv_lat);
        bb:=Basis(Mv_lat);
        zb_Mv_lat_inLd:=[z*bb[i]:z in Basis(ci[i]),i in [1..#bb]]; 
        gens_Mv:=[ (bar_onLd(Ld!g))@@mALd : g in zb_Mv_lat_inLd ];
//zb_Mv_lat_inLd:=[sigma(z)*bar_onLd(bb[i]):z in Basis(ci[i]),i in [1..#bb]]; 
//gens_Mv:=[ g@@mALd : g in zb_Mv_lat_inLd ];
        Mv:=Ideal(WR,gens_Mv);
        /* OLD BROKEN CODE. DOES NOT FINISH
        got_pseudo_basis:=false;
        repeat
            printf ".";
            W:=Integers(L);
            zi_s:=[ Random(M) : i in [1..d] ];
            zi_s_inLd:=[ mALd(z) : z in zi_s ];
            if IsIndependent(zi_s_inLd) then
                // the zi's are an L-basis of A in M
                // now we construct the coefficient ideals wrt to the zi_s
                coeff_ideals:=[];
                for i in [1..#zi_s_inLd] do
                    zi:=zi_s_inLd[i];
                    //proj_onto_zi:=map<A->L| x:->Eltseq(DecomposeVector(sub<Ld|zi>,mALd(x)))[1]>; 
                        //this is wrong, but it works more often the the correct one
                    zi_dot_zi:=DotProduct(zi,zi);
                    proj_onto_zi:=map<A->L| x:->DotProduct(mALd(x),zi)/zi_dot_zi>;
                    ai:=ideal<W|[proj_onto_zi(zM):zM in zbM]>;
                    Basis(ai),ai;
                    Append(~coeff_ideals,ai);
                end for;
                // we check if we got a pseudo basis
                gens_Mtest_inLd:=&cat([[zi_s_inLd[i]*c : c in Basis(coeff_ideals[i])] : i in [1..#zi_s_inLd]]);
                gens_Mtest_inA:=[ g@@mALd : g in gens_Mtest_inLd ];
                M_test:=Ideal(Order(M),gens_Mtest_inA);
                Index(M_test,M);
                got_pseudo_basis:=M_test eq M;
            end if;
        until got_pseudo_basis; 
        printf "\n";
        // We got a pseudo-basis. 
        

        // We construct Tr_A/L
        // for every x in A, I need the matrix m_x corresponding to "multiplication by x",
        // wrt to any L-basis of A.
        L_basis_ofA:=[ pi_A^i : i in [0..d-1] ];
        TrAL:=map<A->L|x:->Trace(Matrix([mALd(x*b):b in L_basis_ofA]))>;
        // now we follow the code for the TraceDualIdeal
        B:=zi_s;
        BLd:=zi_s_inLd;
        Q:=MatrixRing(L,d)![TrAL(B[i]*B[j]):i,j in [1..d]];
        QQ:=Q^-1;
        BB:=[(&+[ (QQ[i,j]*BLd[j]): j in [1..d]])@@mALd : i in [1..d]] ;
        assert forall{i:i,j in [1..d]|TrAL(B[i]*BB[j]) eq KroneckerDelta(i,j)};
        // BB contains the dual basis of zi's
        coeff_ideals_invs:=[ I^-1 : I in coeff_ideals ]; 
        BB_inLd:=[mALd(b):b in BB];
        gens_inLd:=&cat[[ BB_inLd[i]*c : c in Basis(coeff_ideals_invs[i]) ]: i in [1..d]];
        Mv:=Ideal(Order(M),[(bar_onLd(g))@@mALd:g in gens_inLd]);
        */

        //////////////////////////////////////////
        // now we do Iv, by locally glueing \bar{I}^t at every ell neq p and Delta^-1(Mv) at p. 
        K_coprime_p:=TraceDualIdeal(ComplexConjugate(I));
        K_p:=Delta_inverse_ppart(isog,Mv);
        ind:=Index(K_p+K_coprime_p,K_p meet K_coprime_p);
        k:=Valuation(ind,p);
        pk:=p^k;
        ind_coprime_p:=ind div pk;
        Iv:=pk*K_coprime_p+ind_coprime_p*K_p;
        AV`DualAbVarFq:=<Iv,Mv>;
    end if;
    return Explode(AV`DualAbVarFq);
end intrinsic;

