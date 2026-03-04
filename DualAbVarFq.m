/* vim: set syntax=magma : */

// TODO add licence

declare attributes AbelianVarietyFq : DualAbVarFq;

//TODO thsis import is not nice..I should probaly store Delta_inverse_ppart in an attribute
import "/home/stmar/IsomClAbVarFqCommEndAlg/GenDeligneModules.m" : Delta_inverse_ppart;
import "/home/stmar/AlgEt/AlgEtQ/Ord.m" : MatrixAtoQ, MatrixQtoA;

intrinsic DualAbelianVarietyCommEndAlg(AV::AbelianVarietyFq)->AlgEtQIdl,AlgEtQIdl
{Given an abelian variety over Fq with commutative endomorphism algebra, returns the generalized deligne module of the dual variety.}
    if not assigned AV`DualAbVarFq then
        // If M is a WR{F,V}-ideal representing the local-local part of the p-divisible group
        // of the abelian variety AV, then the local-local part of the p-divisible group of the
        // dual abelian variety AV^v is represented by the WR{F,V}-ideal M^v which is defined by
        //      M^v = 1/delta * bar(M)^t, where ^t denotes the dual with respect to the Trace(A/L).
        // The element delta is constructed from alpha in the intrinsic _AlphaAtPrecision, used to
        // compute the semilinear operator F and V, at finite precision.
        I,M:=GeneralizedDeligneModule(AV); //I don't think we need to work with the Generalized Deligne Module
        q:=FiniteField(AV);
        p:=CharacteristicFiniteField(AV);
        isog:=IsogenyClass(AV);
        L,_,PL,_,A,pi_A,_,_,WR,_,_,_,_,A_as_vector_space_over_L_data,bar_onA:=DieudonneAlgebraCommEndAlg(isog);
        mAD,mLdD,mALd:=Explode(A_as_vector_space_over_L_data);
        Ld:=Codomain(mALd);
        // - Ld and D are both L-vector spaces of dimension d:=dim_L(A).
        // - mAD is the L-linear isomorphism  that represents A as \prod_i L[x]/g_i where h=\prod_i g_i in L[x], 
        // that is, the i-th component L[x]/g_i is seen as an L-vector space using the power basis.
        // - Ld is the KSpace L^d.
        // - mLdD is the isomorphism Ld->D where the image of the canonial basis is given by 
        //   the images of the powers of pi in D.
        // - mALd = is the composition of mAD with mLdD^-1

        // We convert M into a Lattice over W.
        // Once we compute the right Gram matrix, we can take the dual with respect to that.
        L_basis_ofA:=[ pi_A^i : i in [0..Dimension(Ld)-1] ];
        TrAL:=map<A->L|x:->Trace(Matrix([mALd(x*b):b in L_basis_ofA]))>;
        zbM:=ZBasis(M);
        zbM_inLd:=[mALd(z):z in zbM];
        M_lat:=NumberFieldLattice(zbM_inLd);
        bM_lat:=Basis(M_lat); //over W
        assert M eq Ideal(WR,&cat[[(bb[i]*c)@@mALd:c in Basis(cc[i])] : i in [1..#bb]]) 
                where bb:=Basis(M_lat) where cc:=CoefficientIdeals(M_lat);
        bM_lat_inA:=[b@@mALd:b in bM_lat];
        Gram_M:=MatrixRing(L,Dimension(Ld))![TrAL(x*y):x,y in bM_lat_inA];
        M_lat:=NumberFieldLattice(bM_lat : Gram:=Gram_M);
        Mt_lat:=Dual(M_lat);
        assert forall{i:i,j in [1..#Basis(M_lat)]| TrAL(Basis(M_lat)[i]@@mALd*Basis(Mt_lat)[j]@@mALd) eq KroneckerDelta(i,j)};
        ci:=CoefficientIdeals(Mt_lat);
        bb:=Basis(Mt_lat);
        zb_Mt_lat_inLd:=[z*bb[i]:z in Basis(ci[i]),i in [1..#bb]]; 
        gens_Mt:=[ (Ld!g)@@mALd : g in zb_Mt_lat_inLd ];
        gens_Mv:=[ bar_onA(g) : g in gens_Mt ];

        if IsOrdinary(isog) then
            delta:=One(A);
        else
            if not assigned isog`delta_Hilbert90 then
                error "Rerun the computation of the isomorphism classes with the DualsCompatible vararg set to true";
            end if;
            delta:=isog`delta_Hilbert90;
        end if;
        Mv:=delta^-1*Ideal(WR,gens_Mv);

        // FIXME is the following correct, or should I just work at the local-local maximal ideal of WR ?
        // To compute Iv, we glueing the local parts of bar{I}^t at every ell neq p and Delta^-1(Mv) at p. 
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

