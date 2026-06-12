/*

*/

    sprint:=function(x)
        return StripWhiteSpace(Sprint(x));
    end function;

    SetAssertions(2);
    SetColumns(0);
    AttachSpec("~/AbVarFq/spec");
    AttachSpec("~/AlgEt/specMod");
    AttachSpec("~/AlgEt/specMtrx");
    AttachSpec("~/IsomClAbVarFqCommEndAlg/spec");
    file_out:="~/IsomClAbVarFqCommEndAlg/tests/wkicmWR/output.m";

    PP<x>:=PolynomialRing(Integers());
    cc:=[StringToInteger(c):c in Split(s,"[,]")];
    h:=PP!cc;

    isog:=IsogenyClass(h);
    _,_,_,_,_,_,_,_,WR:=DieudonneAlgebraCommEndAlg(isog);
    t0:=Cputime();
    new:=#WeakEquivalenceClassMonoidWR(isog);
    t_new:=Cputime(t0);

    isog:=IsogenyClass(h);
    _,_,_,_,_,_,_,_,WR:=DieudonneAlgebraCommEndAlg(isog);
    t0:=Cputime();
    old:=#WKICM(WR);
    t_old:=Cputime(t0);

    test:=new eq old select "OK " else "ERR";

    p:=CharacteristicFiniteField(isog);
    q:=FiniteField(isog);
    a:=Ilog(p,q);
    R:=ZFVOrder(isog);
    E:=DeligneAlgebra(isog);
    pi:=PrimitiveElement(E);
    pps:=PrimesAbove(p*R);
    pps0:=[P:P in pps|not pi in P and q/pi in P];
    gnus:=[GCD(a,Ilog(p,Index(R,P))):P in pps0];

    out:=Sprintf("%o\tt_old=%o\tt_new=%o\tgnus_0=%o\t%o",test,t_old,t_new,sprint(gnus),s);
    printf "%o\n",out;
    fprintf file_out,"%o\n",out;

