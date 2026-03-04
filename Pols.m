/* vim: set syntax=magma : */
// TODO add licence

    import "~/IsomClAbVarFqCommEndAlg/GenDeligneModules.m" : Delta_ideal;
    // FIXME get rid of this import. See comment in the corresponding file



    intrinsic PrincipalPolarizationsUpToIsomorphism(AV::AbVarFq,PHI::AlgEtQCMType)->SeqEnum[AlgEtQElts]
    {}
    // FIXME finish this
        p:=CharacteristicFiniteField(AV);
        I,M:=GeneralizedDeligneModule(AV);
        Iv,Mv:=DualAbelianVarietyCommEndAlg(AV);
        
        S:=EndomorphismRing(AV);
        output:=[Algebra(S)|]; //empty list
        if not IsConjugateStable(S) then
            return output;
        end if;
        test,x0:=IsIsomorphic(Iv,I);
        if not test then
            return output;
        end if;
        assert x0*I eq Iv;

        _,_,_,_,_,_,_,Delta_map:=DieudonneAlgebraCommEndAlg(IsogenyClass(AV));
//Index(N+Mv,N meet Mv) where N:=Delta_map(x0)*M;
        // FIXME is this correct? Or do we need to consider only the (0,1)-part?
        test:=IsCoprime(Index(N+Mv,N meet Mv),p) where N:=Delta_map(x0)*M;
        if not test then
            //"not isom M at p";
            return output;
        end if;

        U,u:=UnitGroup(S);
        Ugens_inE:=[u(U.i):i in [1..Ngens(U)]];
        Q,qq:=quo<U|[U.i+ComplexConjugate(Ugens_inE[i])@@u:i in [1..Ngens(U)]]>;
        trans:=[x@@qq@u:x in Q];
        homs:=Homs(PHI);
        for t in trans do
            lambda:=x0*t;
            assert lambda*I eq Iv;
            if lambda eq -ComplexConjugate(lambda) and
               forall{phi:phi in homs| Im(phi(lambda)) gt 0}
               then
                Append(~output,lambda);
            end if;
        end for;
        //"#output = ",#output;
        return output;
    end intrinsic;
