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

declare verbose alpha_at_precision,3;

declare attributes IsogenyClassFq : AlphaWType,
                                    SemilinearOperators;

///////////////////////////////////////////////////////////////////////////////
///////////////////////////Alpha of W-type/////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

intrinsic AlphaWTypeAtPlace(isog::IsogenyClassFq,nu::AlgEtQIdl,m::RngIntElt)->AlgEtQElt
{Given an isogeny class isog, a place nu of the DeligneAlgebra and a positive integer m, returns an integral element alpha of the DieudonneAlgebra A whose image in the quotient (OA/p^mOA)_nu is congruent to the nu-component alpha_nu of an element of of W-type, that is, such that alpha'_nu=(1,....,1,u) where N_(LE_nu/E_nu)(u)=pi_nu.}
    if not assigned isog`AlphaWType then
        isog`AlphaWType:=AssociativeArray();
    end if;
    nu_Hash:=myHash(nu);
    if not IsDefined(isog`AlphaWType,nu_Hash) then
        uniformizers_at_nus:=UniformizersInQFAt_p(plE_sl_in01);
        //FIXME check verbose
        vprintf alpha_at_precision,1 : "Computing alpha_Q for %oth place of %o...",inu,#plE_sl_in01;
        // Can add DUALITY here
        PPs_nu:=PlacesOfDieudonneAlgebraAbovePlaceOfQF(isog,nu);
        f_nu:=InertiaDegree(nu);
        g_nu:=GCD(a,f_nu); //q=p^a
        assert #PPs_nu eq g_nu;

        Rs_nu:=[];
        rs_nu:=<>;
        Us_nu:=[];
        us_nu:=<>;
        PPs_nu_m:=[];
        for PP in PPs_nu do
            PP_m:=PP^(RamificationIndex(PP)*m);
            Append(~PPs_nu_m,PP_m);
            R,r:=ResidueRing(OA,PP_m);
            vprintf alpha_at_precision,2 : "\n\tR,r computed\n";
            U,u:=ResidueRingUnits(OA,PP_m);
            vprintf alpha_at_precision,2 : "\tU,u computed\n";
            Append(~Rs_nu,R);
            Append(~rs_nu,r);
            Append(~Us_nu,U);
            Append(~us_nu,u);
        end for;
        PPs_nu_m_prod:=&*PPs_nu_m;
        Append(~PPs_nus_prod_powers,PPs_nu_m_prod);

        Q,embs,projs:=DirectSum(Rs_nu);
        pr:=map<Algebra(OA) -> Q | x:->&+[embs[i](rs_nu[i](x)) : i in [1..g_nu]], 
                                   y:->CRT( PPs_nu_m ,[projs[i](y)@@rs_nu[i] : i in [1..g_nu]])>;
        pi_Q:=pr(pi_A);
        assert2 forall{ x : x in Generators(Q) | pr(x@@pr) eq x};

        U,U_embs,U_projs:=DirectSum(Us_nu);
        U_pr:=map<Algebra(OA) -> U | x:->&+[U_embs[i](x@@us_nu[i]) : i in [1..g_nu]], 
                                     y:->CRT( PPs_nu_m ,[(U_projs[i](y))@us_nu[i] : i in [1..g_nu]])>;
        sigma_U:=hom<U->U | [U.i@@U_pr@qI@sigma@@qI@U_pr : i in [1..Ngens(U)]]>; 
        assert2 forall{ x : x in Generators(U) | U_pr(x@@U_pr) eq x};

        vprintf alpha_at_precision,2 : "\tQ and U are computed\n";

        image_phi:=function(gamma)
            // gamma in US_nu[gnu] = (OA/PP_{nu,gnu}^m)^*
            // phi does the following two steps
            // 1) gamma :-> beta = (1,...,1,gamma) in U = \prod_i US_nu[i] = OA/\prod_i PP_{nu,i}^m
            // 2) beta :-> beta*beta^sigma_Q*...*beta^(sigma_Q^(a-1)) in U
            beta:=&*[i lt g_nu select U_embs[i]((One(A))@@us_nu[i]) else U_embs[i](gamma):i in [1..g_nu]];
            // Action of the Frobenius on U
            img:=(&*[ i eq 1 select beta else sigma_U(Self(i-1)) : i in [1..a] ]); //in U
            vprintf alpha_at_precision,2 : "\timg = %o\n\tsigma(img) = %o\n",img,sigma_U(img);
            assert2 sigma_U(img) eq img;
            return img;
        end function;
        phi:=hom<Us_nu[g_nu]->U | [ image_phi(Us_nu[g_nu].i) : i in [1..Ngens(Us_nu[g_nu])]] >;
        
        u_nu:=uniformizers_at_nus[inu]; // in E
        val_nu:=Valuation(pi,nu); // in E
        // We want to compute wU in U representing the unit pi/u_nu^val_nu.
        // By constuction, this quotient is an invertible element of the completion OA_nu,
        // but it might not be an element of OA, since u_nu is picked as an element which is a unit
        // at every place of E above p (of slope in (0,1) ). 
        // This is an issues since we can only take preimages to U from OA.
        // So, we use the following workaround:
        // w_nu is in OE and congrunent to u_nu^val_nu/pi at nu and 1 at every other place above p
        // The precision is chosen to be a majorative of RamificationIndex(pp)*m [to match the quotient we are using]
        // plus Valuation(PP,pi) leq Valuation(PP,q)=RamificationIndex(pp)*a.
        pE:=PlacesOfQFAbove_p(isog);
        w_nu:=CRT([pp^(Dimension(E)*(m+a)):pp in pE],[pp eq nu select u_nu^val_nu else pi : pp in pE])/pi; // in OE
        wU:=-U_pr(Delta_map(w_nu)); // in E->A->U

        gamma0:=wU@@phi; // in Us[g_nu], the last componenet of U
        gamma_A:=(&+[i lt g_nu select 
                                U_embs[i](One(A)@@us_nu[i]) else 
                                U_embs[i](gamma0) : i in [1..g_nu]])@@U_pr; // in A
        u0:=Delta_map(u_nu^(Integers()!(val_nu*g_nu/a)));
        beta_A:=(&+[i lt g_nu select 
                                embs[i](rs_nu[i](One(A))) else 
                                embs[i](rs_nu[i](u0)) : i in [1..g_nu]])@@pr; 
        alpha:=gamma_A*beta_A;
        isog`AlphaWType[nu_Hash]:=alpha;
    end if;
    return isog`AlphaWType[nu_Hash];
end intrinsic;

///////////////////////////////////////////////////////////////////////////////////
///////////////////////////SemilinearOperators/////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////

intrinsic SemilinearOperatorsAtPlaces(isog::IsogenyClassFq,J::AlgEtQIdl,nu::AlgEtQIdl,m::RngIntElt)->//TODO
{}
end intrinsic;

intrinsic SemilinearOperators(isog::IsogenyClassFq,J::AlgEtQIdl,nu::AlgEtQIdl,m::RngIntElt)->//TODO
{}
//TODO DIRECT SUM or CRT?
end intrinsic;

// OLD VERSION
//intrinsic SemilinearOperators(isog::IsogenyClassFq)->RngIntElt,AlgEtQIdl,AlgEtQIdl,GrpAb,Map,Map,Map
//{Returns the homonymous attribute of the isogeny class, which consists of the following informations: m0,J,den_ideal,Qm0,qm0,FQm0,VQm0, where (see DieudonneAlgebraCommEndAlg for the missing definitions):
//- m0 is a positive integer;
//- J is a WR-ideal with maximal endomorphism ring OA which is stable under the action of F and V=pF^-1, for some semilinear operator F with the Frobenius property of and of W-type;
//- den_ideal = p^m0*J+P01^M*J, where P01 is the product of the maximal ideals of WR which are above the unique local-local maximal ideal of R, and M is chosen so that P01^MJ c J locally at every such maximal ideal;
//- Qm0 is the abelian group J/den_ideal and qm0 is the quotient map J->Qm0;
//- FQm0 and Vm0 are additive maps induced by semilinear operators F and V as above. They represent the Frobenius and Verschiebung acting on Dieudonné modules.
//The attribute SemilinearOperators needs to be computed beforehand, during a run of IsomorphismClassesDieudonneModulesCommEndAlg. During this run, the integer m0 is automatically computed by the program to guarantee that every fractional W'R-ideal I' whose extension to OA is F and V stable such that I' c J and den_ideal c I'. These two conditions allow us to verify if I' is a W'R\{F,V\} ideal, that is, (the local-local-part) of a Dieudonne module of some abelian variety in isog.}
//    //TODO: in the future it would be nice to be able to increase the precision with a call of this intrinsic.
//    // This would require to choose a new alpha (as in alpha_at_precision) 'compatible' with the current choice.
//    // I might be a bit complicated to code, and it is outside of the current scope.
//    require assigned isog`SemilinearOperators : "Run first IsomorphismClassesDieudonneModules(isog)";
//    return Explode(isog`SemilinearOperators);
//end intrinsic;

