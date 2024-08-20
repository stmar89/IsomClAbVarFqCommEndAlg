/* vim: set syntax=magma : */

intrinsic save_isom_classes(classes::SeqEnum)-> .
{ We get a sequence of elments of the form <I,dm,L,S>, where :
 - I is an fractional R-ideal in E=Q[pi], where R=Z[pi,q/pi];
 - dm is a fractional WR-ideal in A;
 - L is an invertible S-ideal in E;
 - S is an order in E, determined as the End of I and dm.
 Returns a string that contains all the data. 
 This string can be loaded using load_isom_classes, defined below. }
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
    assert assigned R`SemilinearOperators;
    m0,J,den_idl,Qm0,qm0,FQm0,VQm0:=Explode(R`SemilinearOperators);
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

intrinsic load_isom_classes(input::MonStgElt)-> .
{ input: the string produced by save_isom_classes
  output: a sequence of tuples <I,dm,L,S>, as produced by IsomorphismClassesAbelianVarieties.
  R`SemilinearOperators is populated with the information about the computation of the semilinear F and V on the Dieudonne modules.}
    input:=eval(input);
    PP<x>:=PolynomialRing(Integers());
    E:=EtaleAlgebra([NumberField(PP!f) : f in input[1]]);
    h:=DefiningPolynomial(E);
    pi:=PrimitiveElement(E);
    q:=Round(ConstantCoefficient(h)^(2/Degree(h)));
    R:=Order([pi,q/pi]);
    A:=EtaleAlgebra([NumberField(PP!f) : f in input[2]]);
    WR:=Order([A!z : z in input[3]]);
    ends:=[Order([E!z : z in S]) : S in input[4]];
    pics:=[* [ Ideal(ends[i_picS],[E!z : z in L]) : L in input[5,i_picS] ] : i_picS in [1..#input[5]] *];
    Is:=[ Ideal(R,[E!z:z in I]) : I in input[6] ];
    dms:=[ Ideal(WR,[A!z:z in dm]) : dm in input[7] ];
    output:=[];
    for iso in input[8] do
        Append(~output, < Is[iso[1]] , dms[iso[2]] , pics[iso[4],iso[3]] , ends[iso[4]] >);
    end for;

    _,p,a:=IsPrimePower(q);
    slinop:=input[9];
    m0:=slinop[1];
    J:=Ideal(WR,[A!z:z in slinop[2]]);
    J`ZBasis:=[A!z : z in slinop[2]]; // the ideal creation does an HNF of the ZBasis.
                                      // this messes up the info about the quotient below.
    den_idl:=Ideal(WR,[A!z:z in slinop[3]]);
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
    R`SemilinearOperators:=<m0,J,den_idl,Qm0,qm0,FQm0,VQm0>;
    return output;
end intrinsic;


/*
    
    AttachSpec("~/AlgEt/spec");
    Attach("PrimesAttributes.m");
    Attach("DieudonneModules.m");
    Attach("IsomorphismClasses.m");
    Attach("SaveLoad.m");

    PP<x>:=PolynomialRing(Integers());

    hs:=[
        x^4 - 9*x^3 + 36*x^2 - 72*x + 64, // 1 iso
        x^2 - 3*x + 9,
        x^2 + 9,
        PP![ 16, 8, 8, 2, 1 ] //4 classes
        ];

    for h in hs do
        q:=Truncate(ConstantCoefficient(h)^(2/Degree(h)));
        E:=EtaleAlgebra(h);
        pi:=PrimitiveElement(E);
        R:=Order([pi,q/pi]);
        time iso:=IsomorphismClassesAbelianVarieties(R);

        str:=save_isom_classes(iso);
        delete q,E,pi,R;
        iso_test:=load_isom_classes(str);
        assert #iso eq #iso_test;
        for i in [1..#iso_test] do
            cl:=iso[i];
            cl_test:=iso_test[i];
            I:=cl[1]; _:=I eq 2*I; //to assign the Hash
            I_test:=cl_test[1]; _:=I_test eq 2*I_test; //to assign the Hash
            assert I_test`Hash eq I`Hash;
            I:=cl[2]; _:=I eq 2*I; //to assign the Hash
            I_test:=cl_test[2]; _:=I_test eq 2*I_test; //to assign the Hash
            assert I_test`Hash eq I`Hash;
            I:=cl[3]; _:=I eq 2*I; //to assign the Hash
            I_test:=cl_test[3]; _:=I_test eq 2*I_test; //to assign the Hash
            assert I_test`Hash eq I`Hash;
            assert cl_test[4]`Hash eq cl[4]`Hash;
        end for;
        R:=Order(iso_test[1,1]);
        _,J,dJ,Q,qm,F,V:=Explode(R`SemilinearOperators);
        assert #Q eq #Quotient(J,dJ);
        for cl in iso_test do
            M:=cl[2];
            assert M subset J;
            MQ:=sub<Q|[qm(z):z in ZBasis(M)]>;
            FMQ:=sub<Q|[F(MQ.i):i in [1..Ngens(MQ)]]>;
            VMQ:=sub<Q|[V(MQ.i):i in [1..Ngens(MQ)]]>;
            assert FMQ+VMQ subset MQ;
        end for;
    end for;

*/






