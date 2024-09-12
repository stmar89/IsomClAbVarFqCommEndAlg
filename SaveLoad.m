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

intrinsic SaveAbVarFqCommEndAlg(classes::SeqEnum[AbelianVarietyFq])->MonStgElt
{Given a sequence of abelian vareities belonging to an isogney class over Fq with commutative Fq-endomorphism algebra, returns a string containing all the info about the isomorphism classes of the varietis. This string can be loaded using LoadAbVarFqCommEndAlg defined below.}
    isog:=IsogenyClass(classes[1]);
    require forall{A:A in classes|IsogenyClass(A) eq isog} : "The abelian varieties need to belong to the same isogeny class.";
    require IsSquarefree(isog) : "The isogeny class needs to have squarefree Weil polynomial.";
    classes0:=[];
    for A in classes do
        tup:=A`IsomDataCommEndAlg;
        Append(~classes0,tup);
    end for;
    classes:=classes0;

    E:=Algebra(classes[1,1]);
    E:=[ Coefficients(DefiningPolynomial(F)) : F in Components(E) ];
    E:=Sprint(E);
    A:=Algebra(classes[1,2]);
    A:=[ Coefficients(DefiningPolynomial(F)) : F in Components(A) ];
    A:=Sprint(A);
    WR:=Order(classes[1,2]);
    _,WR:=PrintSeqAlgEtQElt(ZBasis(WR));
    ends:={@ iso[4] : iso in classes @};
    pics:=[* [ iso[3] : iso in classes | Order(iso[3]) eq S ] : S in ends *];
    Is:={@ iso[1] : iso in classes @};
    dms:={@ iso[2] : iso in classes @};
    isom_classes_as_indices:=[];
    for iso in classes do
        I:=Index(Is,iso[1]);
        dm:=Index(dms,iso[2]);
        S:=Index(ends,iso[4]);
        L:=Index(pics[S],iso[3]);
        assert I ne 0 and dm ne 0 and S ne 0 and L ne 0;
        Append(~isom_classes_as_indices,[I,dm,L,S]);
    end for;
    isom_classes_as_indices:=Sprint(isom_classes_as_indices);

    ends_str:="[" cat Prune(&cat[ strS cat "," where _,strS:=PrintSeqAlgEtQElt(ZBasis(S)) : S in ends ]) cat "]";
    Is_str:="[" cat Prune(&cat[ strI cat "," where _,strI:=PrintSeqAlgEtQElt(ZBasis(I)) : I in Is ]) cat "]";
    dms_str:="[" cat Prune(&cat[ strdm cat "," where _,strdm:=PrintSeqAlgEtQElt(ZBasis(dm)): dm in dms ]) cat "]";
    pics_str:="[";
    for picS in pics do
        picS_str:="[";
        for L in picS do
            _,strL:=PrintSeqAlgEtQElt(ZBasis(L));
            picS_str cat:=strL cat ",";
        end for;
        Prune(~picS_str);
        picS_str cat:="]";
        pics_str cat:=picS_str cat ",";
    end for;
    Prune(~pics_str);
    pics_str cat:="]";

    R:=Order(classes[1,1]);
    assert assigned isog`SemilinearOperators;
    m0,J,den_idl,Qm0,qm0,FQm0,VQm0:=Explode(isog`SemilinearOperators);
    _,zbJ:=PrintSeqAlgEtQElt(ZBasis(J));
    _,zbden:=PrintSeqAlgEtQElt(ZBasis(den_idl));
    _,imgsF:=PrintSeqAlgEtQElt([(FQm0(Qm0.i))@@qm0 : i in [1..Ngens(Qm0)]]); //in J
    _,imgsV:=PrintSeqAlgEtQElt([(VQm0(Qm0.i))@@qm0 : i in [1..Ngens(Qm0)]]); //in J
    slinop_str:=Sprintf("<%o,%o,%o,%o,%o>",m0,zbJ,zbden,imgsF,imgsV);

    output:="<" cat E cat "," cat A cat "," cat WR cat "," cat 
                ends_str cat "," cat 
                pics_str cat "," cat
                Is_str cat "," cat
                dms_str cat "," cat
                isom_classes_as_indices cat "," cat 
                slinop_str cat ">"; 
    output:=&cat(Split(output)); // remove \n
    return output;
end intrinsic;

intrinsic LoadAbVarFqCommEndAlg(isog::IsogenyClassFq,input::MonStgElt)->SeqEnum[AbelianVarietyFq]
{Given an isogeny class of abelian varieties over Fq with commutative Fq-endomorphism algebra and the string produced by SaveAbVarFqCommEndAlg, returns the sequence of abelian varieties which is stored in the string. The SemilinearOperator attribute of isog is populated (see SemilinearOperators for details).}
    input:=eval(input);
    PP<x>:=PolynomialRing(Integers());
    /*
    E:=EtaleAlgebra([NumberField(PP!f) : f in input[1]]);
    h:=DefiningPolynomial(E);
    pi:=PrimitiveElement(E);
    q:=Round(ConstantCoefficient(h)^(2/Degree(h)));
    R:=Order([pi,q/pi]);
    */
    R:=ZFVOrder(isog);
    E:=Algebra(R);
    A:=EtaleAlgebra([NumberField(PP!f) : f in input[2]]);
    WR:=Order([A!z : z in input[3]]);
    ends:=[Order([E!z : z in S]) : S in input[4]];
    pics:=[* [ Ideal(ends[i_picS],[E!z : z in L]) : L in input[5,i_picS] ] : i_picS in [1..#input[5]] *];
    Is:=[ Ideal(R,[E!z:z in I]) : I in input[6] ];
    dms:=[ Ideal(WR,[A!z:z in dm]) : dm in input[7] ];
    output:=[];
    for iso in input[8] do
        AV:=AbelianVarietyCommEndAlg(isog,<Is[iso[1]],dms[iso[2]],pics[iso[4],iso[3]],ends[iso[4]]>);
        AV`EndomorphismRing:=ends[iso[4]];
        Append(~output,AV);
    end for;

    slinop:=input[9];
    m0:=slinop[1];
    J:=Ideal(WR,[A!z:z in slinop[2]]);
    J`ZBasis:=[A!z : z in slinop[2]]; // the ideal creation does an HNF of the ZBasis.
                                      // this messes up the info about the quotient below.
    den_idl:=Ideal(WR,[A!z:z in slinop[3]]);
    p:=CharacteristicFiniteField(isog);
    assert p^m0*J subset den_idl;
    Qm0,qm0:=Quotient(J,den_idl);
    assert Index(J,den_idl) eq #Qm0;
    imgsF:=[A!z:z in slinop[4]];
    imgsV:=[A!z:z in slinop[5]];
    assert forall{z:z in imgsF|z in J};
    assert forall{z:z in imgsV|z in J};
    imgsF:=[qm0(z):z in imgsF];
    imgsV:=[qm0(z):z in imgsV];
    FQm0:=hom<Qm0->Qm0|imgsF>;
    VQm0:=hom<Qm0->Qm0|imgsV>;
    assert forall{i:i in [1..Ngens(Qm0)] | FQm0(VQm0(Qm0.i)) eq p*Qm0.i};
    assert forall{i:i in [1..Ngens(Qm0)] | VQm0(FQm0(Qm0.i)) eq p*Qm0.i};
    isog`SemilinearOperators:=<m0,J,den_idl,Qm0,qm0,FQm0,VQm0>;
    return output;
end intrinsic;

