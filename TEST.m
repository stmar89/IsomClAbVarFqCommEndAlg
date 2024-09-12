/* vim: set syntax=magma : */

    AttachSpec("~/AlgEt/spec");
    AttachSpec("~/AlgEt/specMod");
    AttachSpec("~/AlgEt/specMtrx");
    AttachSpec("~/AbVarFq/spec");
    AttachSpec("~/IsomClassesAbVarFqComEnd/spec");
    //AttachSpec("~/IsomClAbVarFqCommEndAlg/spec");

    PP<x>:=PolynomialRing(Integers());

    hs:=[
        x^4 - 9*x^3 + 36*x^2 - 72*x + 64, // 1 iso
        x^2 - 3*x + 9,
        x^2 + 9,
        PP![ 16, 8, 8, 2, 1 ], //4 classes
        x^4 + 4*x^2 + 16
        ];

    for h in hs do
        h;
        isog:=IsogenyClass(h);
        time iso:=IsomorphismClasses(isog);
        str:=SaveAbVarFqCommEndAlg(iso);
        delete isog;
        isog:=IsogenyClass(h);
        iso_test:=LoadAbVarFqCommEndAlg(isog,str);
        assert #iso eq #iso_test;
        _,J,dJ,Q,qm,F,V:=SemilinearOperators(isog);
        assert #Q eq #Quotient(J,dJ);
        for i in [1..#iso_test] do
            I,M,L,S:=IsomDataCommEndAlg(iso[i]);
            II,MM,LL,SS:=IsomDataCommEndAlg(iso_test[i]);
            _:=I eq 2*I; //to assign the Hash
            _:=II eq 2*II; //to assign the Hash
            _:=M eq 2*M; //to assign the Hash
            _:=MM eq 2*MM; //to assign the Hash
            _:=L eq 2*L; //to assign the Hash
            _:=LL eq 2*LL; //to assign the Hash
            assert II`Hash eq I`Hash;
            assert MM`Hash eq M`Hash;
            assert LL`Hash eq L`Hash;
            assert S`Hash eq SS`Hash;
            assert MM subset J;
            MQ:=sub<Q|[qm(z):z in ZBasis(MM)]>;
            FMQ:=sub<Q|[F(MQ.i):i in [1..Ngens(MQ)]]>;
            VMQ:=sub<Q|[V(MQ.i):i in [1..Ngens(MQ)]]>;
            assert FMQ+VMQ subset MQ;
        end for;
    end for;
