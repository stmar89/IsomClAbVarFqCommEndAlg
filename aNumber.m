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
// Copyright 2026, S. Marseglia
/////////////////////////////////////////////////////

declare attributes AbelianVarietyFq : aNumber;

intrinsic aNumber(AV:AbelianVarietyFq)->RngIntElt
{Returns the a-number of the abelian vareity. The SemilinearOperators need to have been computed at precision m0>0.}
    if not assigned AV`aNumber then
        require assigned AV`IsomDataCommEndAlg : "The attribute IsomDataCommEndAlg is not assigned";
        isog:=IsogenyClass(AV);
        require IsSquarefree(isog) : "At the moment it is implemented only for abelian varieties with commutative Fq-endomorphism algebra.";
        Q,mQ,F,V,dJ,m0,J:=SemilinearOperators(isog);
        require m0 gt 0 : "The SemilinearOperators need to be computed at positive precision. Rerun IsomorphismClassesCommEndAlg with the parameter IncreaseMinimumPrecisionForSemilinearFVBy set to 1";
        _,dm:=IsomDataCommEndAlg(AV);
        assert dm subset J;
        M:=sub<Q|[mQ(z):z in ZBasis(dm)]>;
        FM:=sub<M|[M!F(M.i):i in [1..Ngens(M)]]>;
        VM:=sub<M|[M!V(M.i):i in [1..Ngens(M)]]>;
        q:=FiniteField(isog);
        a_num:=Ilog(q,Index(M,FM+VM));
        AV`aNumber:=a_num;
    end if;
    return AV`aNumber;
end intrinsic;

/*
    
*/
