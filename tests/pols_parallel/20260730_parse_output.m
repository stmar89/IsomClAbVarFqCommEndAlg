   
    _<x>:=PolynomialRing(Integers());
    all:=Split(Read("~/IsomClAbVarFqCommEndAlg/tests/pols_parallel/20260730_correct.txt"));
    data:=AssociativeArray(:Default:=0);
    for l in all do
        h:=eval(Split(l,":")[1]);
        g:=Degree(h) div 2;
        a:=StringToInteger(Split(Split(l,":")[2],"=")[2]);
        irr:=IsIrreducible(h);
        if irr then
            data[<g,a,"irr">]+:=1;
        else
            data[<g,a,"not_irr">]+:=1;
        end if;
    end for;
    for k in Sort(Setseq(Keys(data))) do
        printf "g=%o, a=%o, irreducible=%o,\tcomputed=%o\n",k[1],k[2],k[3] eq "irr",data[k];
    end for;
