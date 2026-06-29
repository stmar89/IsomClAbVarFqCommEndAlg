
    PP<x>:=PolynomialRing(Integers());
    AttachSpec("~/AbVarFq/spec");
    AttachSpec("~/AlgEt/specMod");
    AttachSpec("~/AlgEt/specMtrx");
    AttachSpec("~/IsomClAbVarFqCommEndAlg/spec");
    lines:=Split(Read("~/IsomClAbVarFqCommEndAlg/tests/bar_rho/output.m"));
    for line in lines do
        if "t,t" in line then
            all:=Split(line,":");
            s:=all[#all];
            h:=PP![StringToInteger(c):c in Split(s,"s=[,]")];
            isog:=IsogenyClass(h);
            p0,p01,p1:=PlacesOfQFAbove_p(isog); 
            es:=[RamificationIndex(nu): nu in p01|IsConjugateStable(nu)];
            if exists{e:e in es|IsOdd(e)} then
                line;
            end if;
        end if;
     end for;

