    
    _<x>:=PolynomialRing(Integers());
    all:=Split(Read("~/IsomClAbVarFqCommEndAlg/tests/pols_parallel/20260730_correct.txt"));
    for l in all do
        h:=eval(Split(l,":")[1]);
        if IsIrreducible(h) then
            l;
        end if;
    end for;
