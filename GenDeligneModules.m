/* vim: set syntax=magma : */

/////////////////////////////////////////////////////
// Stefano Marseglia, stefano.marseglia89@gmail.com
// https://stmar89.github.io/index.html
// 
// Distributed under the terms of the GNU Lesser General Public License (L-GPL)
//      http://www.gnu.org/licenses/
// 
// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation; either version 3.0 of the License, or
// (at your option) any later version.
// 
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301  USA
// 
// Copyright 2024, S. Marseglia
/////////////////////////////////////////////////////

declare attributes AbelianVarietyFq : GeneralizedDeligneModule;

declare attributes IsogenyClassFq : glueing_gen_deligne_module_data;


intrinsic GeneralizedDeligneModule(AV:AbelianVarietyFq)->AlgEtQIdl,AlgEtQIdl,MonStgElt
{Given an abelian variety AV, it returns a pair (I,M) where I is a fractional ideal over R=ZFVOrder and M is a fractional ideal over WR (defined in DieudonneAlgebraCommEndAlg) such that I \otimes Zp = Delta_map^-1(M\otimes Zp). The ideal I encodes local information at l\neq p, the étale-local and local-étale information about AV, while M encodes the Dieudonne module.}
    if not assigned AV`GeneralizedDeligneModule then
        require assigned AV`IsomDataCommEndAlg : "The attribute IsomDataCommEndAlg is not assigned";
        isog:=IsogenyClass(AV);
        require IsSquarefree(isog) : "At the moment it is implemented only for abelian varieties with commutative Fq-endomorphism algebra.";
        p:=CharacteristicFiniteField(isog);
        J,DM,L,S,slopesDieudonneModules:=IsomDataCommEndAlg(AV);
        R:=ZFVOrder(isog);
        assert slopesDieudonneModules in {"(0,1)","all"};
        if not assigned isog`glueing_gen_deligne_module_data then
            isog`glueing_gen_deligne_module_data:=AssociativeArray();
        end if;
        already_done,data:=IsDefined(isog`glueing_gen_deligne_module_data,<J,DM>);
        if already_done then
            K,N,slopes_done:=Explode(data);
            assert slopes_done eq slopesDieudonneModules;
        else
            _,_,_,_,_,_,_,Delta_map,WR:=DieudonneAlgebraCommEndAlg(isog);
            // if slopesDieudonneModules eq "(0,1)" then
            // denote by m the local-local ideal of R.
            // need I and M satisfying : 
            //                           M_n = (Delta(JL)*WR)_n for every max R-ideal n above p of slope 0 or 1,
            //                           M_m = (Delta(L)*DM)_m,
            //                           I_p = (Delta^-1(M))_p,
            //                           I_l = (JL)_l for every l!=p.
            //
            // This will be done by computing and storing K and N such that
            //                           N_n = (Delta(J)*WR)_n for every max R-ideal n above p of slope 0 or 1,
            //                           N_m = DM_m,
            //                           K_p = (Delta^-1(N))_p,
            //                           K_l = J_l for every l!=p.
            // Then we set: I = K*L and M = N*Delta(L).
            // ---------------------------------------------------
            // if instead slopesDieudonneModules eq "(0,1)" then
            // DM encodes all the info at p and J encodes all the infor away from p.
            // We need I and M satisfying:
            //                          M_p = (Delta(L)*DM)_p
            //                          I_p = (Delta^-1(M))_p
            //                          I_l = (JL)_l for every l!=p
            // 
            // We store auxiliary modules K and N such that
            //                          N = DM
            //                          K_p = (Delta^-1(N))_p     -- this bit is computationally expensive
            //                          K_l = J_l for every l!=p
            // Then we set: I = K*L and M = N*Delta(L).
            // ---------------------------------------------------
            // NB: only the construction of N is different. Given N and J, we construct K, I and M in the
            // same way.
            if slopesDieudonneModules eq "(0,1)" then
                // We create N
                DeltaJ:=DeltaIdeal(isog,J);
                DeltaJ_DM:=DeltaJ+DM;
                k:=Valuation(Index(DeltaJ_DM,DeltaJ),p)+Valuation(Index(DeltaJ_DM,DM),p);
                mm0,mm01,mm1:=PrimesOfZFVAbove_p(isog);
                m_k:=#mm01 eq 1 select Ideal(WR,[Delta_map(z):z in ZBasis(mm01[1]^k)]) else OneIdeal(WR);
                nn_k:=#mm0+#mm1 eq 0 select OneIdeal(WR) 
                        else Ideal(WR,[Delta_map(z):z in ZBasis(&*([P^k:P in mm0 cat mm1]))]);
                N:=m_k*DeltaJ+nn_k*DM;
            elif slopesDieudonneModules eq "all" then
                N:=DM;
            end if;
            // We create K
            K_p:=R!!DeltaInverseIdealpPart(isog,N);
            K_coprime_p:=J;
            sum:=K_p+K_coprime_p;
            ind:=Index(sum,K_p)*Index(sum,K_coprime_p);
            k:=Valuation(ind,p);
            pk:=p^k;
            ind_coprime_p:=ind div pk;
            K:=pk*K_coprime_p+ind_coprime_p*K_p;
            isog`glueing_gen_deligne_module_data[<J,DM>]:=<K,N,slopesDieudonneModules>;
        end if;
        // We create (I,M)
        I:=K*(R!!L);
        M:=N*DeltaIdeal(isog,L);
        AV`GeneralizedDeligneModule:=<I,M,slopesDieudonneModules>;
    end if;
    return Explode(AV`GeneralizedDeligneModule);
end intrinsic;

