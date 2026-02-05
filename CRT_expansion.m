/////////////////////////////////////////////////////
// An expansion for ChineseRemainderTheoremFunctions
/////////////////////////////////////////////////////

/// Given a fractional $S$-ideal `J` and sequence `Is` of $N$ integral fractional $S$-ideals $I_1,\ldots,I_N$, pairwise coprime, returns a map $J \to J^N$ representing the natural isomorphism $J/I*J \to \frac{J}{I_1*J}\times \cdots \times \frac{J}{I_N*J}$, where $I=\prod_i I_i$, and a map $J^N \to J$ representing the inverse.  
intrinsic ChineseRemainderTheoremFunctions(J::AlgEtQIdl,Is::SeqEnum[AlgEtQIdl])-> Map,Map
{Given a fractional S-ideal J and sequence Is of N integral fractional S-ideals I_1,\ldots,I_N, pairwise coprime, returns a map J \to J^N representing the natural isomorphism J/I*J \to J/I_1*J x ... x J/I_N*J, where I=\prod_i I_i, and a map J^N \to J representing the inverse.}
    S:=Order(Is[1]);
    N:=#Is;
    require forall{i : i in [2..N] | Order(Is[i]) eq S} and Order(J) eq S:"the ideals must be of the same order";
    Q,q:=Quotient(J,&meet(Is)*J);
    quots:=[];
    maps:=<>;
    for I in Is do
        QI,qI:=Quotient(J,I*J);
        Append(~quots,QI);
        Append(~maps,qI);
    end for;
    D,embs,projs:=DirectSum(quots);
    assert IsIsomorphic(D,Q);
    isom:=iso<Q->D | [ &+[embs[j](maps[j](Q.i@@q)) : j in [1..#Is]] : i in [1..Ngens(Q)] ]>;
    // isom : J/&meet(Is)*J -> \prod_{I in Is} J/I*J
    // is the natural isomorphism of S modules.
    // The inverse (constructed by considering isom as an addive map) is automatically S-linear
    func1:=function(x)
        return [projs[j](isom(q(x)))@@maps[j] : j in [1..N] ];
    end function;
    func2:=function(as)
        assert forall{a:a in as|a in J};
        assert #as eq N;
        return (&+[embs[j](maps[j](as[j])) : j in [1..N] ])@@isom@@q;
    end function;
    II:=&meet(Is);
    assert forall{s : s in ZBasis(J) | func2(func1(s)) -s in J*II};
    return func1,func2;
end intrinsic;


/* TESTS

    printf "### Testing CRT:";
    //AttachSpec("~/packages_github/AlgEt/spec");
    SetVerbose("CRT",1);
    SetAssertions(2);

    _<x>:=PolynomialRing(Integers());
    f:=(x^8+16)*(x^8+81);
    A:=EtaleAlgebra(f);
    E1:=EquationOrder(A);

    pp:=PrimesAbove(Conductor(E1));
    pp13:=[ P : P in pp | MinimalInteger(P) eq 13 ];

    pairs:=[];
    for i in [1..10000] do
        repeat
            a:=Random(E1);
        until not a in pp13[1];
        repeat
            b:=Random(E1);
        until not b in pp13[2];
        Append(~pairs,[a,b]);
    end for;
    printf ".";
    // test 1

    out1:=[];
    for pair in pairs do
        a:=pair[1];
        b:=pair[2];
        e:=ChineseRemainderTheorem(pp13[1],pp13[2],a,b);
        Append(~out1,e);
    end for;
    printf ".";
    // old code ~14 secs. new code ~7 secs. w/o profiler

    // test 2
    out2:=[];
    e1:=ChineseRemainderTheorem(pp13[1],pp13[2],A!1,A!0);
    e2:=ChineseRemainderTheorem(pp13[1],pp13[2],A!0,A!1);
    for pair in pairs do
        a:=pair[1];
        b:=pair[2];
        e:=a*e1+b*e2;
        Append(~out2,e);
    end for;
    printf ".";
    pp13:=pp13[1]*pp13[2];
    assert forall{i : i in [1..#out1] | (out1[i] - out2[i]) in pp13};

    // test 3 : >2 primes
    tuples:=[];
    for i in [1..1000] do
        i_tup:=[];
        for j in [1..#pp] do
            repeat
                a:=Random(E1);
            until not a in pp[j];
            Append(~i_tup,a);
        end for;
        Append(~tuples,i_tup);
    end for;

    out3:=[];
    out4:=[];
    for tup in tuples do
        e:=ChineseRemainderTheorem(pp,tup);
        Append(~out3,e);
    end for;

    f,g:=ChineseRemainderTheoremFunctions(pp);
    for tup in tuples do
        e:=g(tup);
        Append(~out4,e);
    end for;

    I:=&meet(pp);
    assert forall{i : i in [1..#out3] | (out3[i] - out4[i]) in I};

    printf ".";


    f:=x^6 - 3*x^5 - 3*x^4 + 65*x^3 - 48*x^2 - 768*x + 4096;
    A:=EtaleAlgebra(f);
    gensT:=[
        <[ 1, 0 ], [ 1/9, 5/6, 1, 41/18 ]>,
        <[ 0, 1 ], [ 0, 1, 0, 0 ]>,
        <[ 0, 0 ], [ 8/9, 11/6, 4/3, 133/18 ]>,
        <[ 0, 0 ], [ 0, 8/3, 7/3, 29/3 ]>,
        <[ 0, 0 ], [ 0, 0, 3, 3 ]>,
        <[ 0, 0 ], [ 0, 0, 0, 18 ]>
    ];
    gensT:=[ A ! g : g in gensT ];
    T:=Order(gensT);
    assert #PicardGroup(T) eq 192;
    printf ".";

    SetAssertions(1);
    printf " all good!";

*/
