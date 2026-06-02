/*
*/
    SetAssertions(1);
    AttachSpec("~/AbVarFq/spec");
    AttachSpec("~/AlgEt/specMod");
    AttachSpec("~/AlgEt/specMtrx");
    AttachSpec("~/IsomClAbVarFqCommEndAlg/spec");
    file_out:="~/IsomClAbVarFqCommEndAlg/tests/gnu_gt_2/input.m";
    PP<x>:=PolynomialRing(Integers());

    c:=[StringToInteger(c):c in Split(cc,"[ ,]")];
    g:=(#c-1) div 2;
    if g ge 2 then
        h:=PP!c;
        if IsSquarefree(h) then
            isog:=IsogenyClass(h:Check:=false);
            p:=CharacteristicFiniteField(isog);
            _,a:=IsPowerOf(FiniteField(isog),p);
            if a gt 2 then
                plE0,plE01,plE1:=PlacesOfQFAbove_p(isog);
                // look for nu such that gnu > 2 and sl(nu)=0, 
                // but forall nu with sl(nu) in (0,1) we have gnu<=2.
                interesting:=exists{P:P in plE0|GCD(InertiaDegree(P),a) gt 2} and
                             forall{P:P in plE01|GCD(InertiaDegree(P),a) le 2};
                if interesting then
                    fprintf file_out,"%o\n",StripWhiteSpace(cc);
                end if;
            end if;
        end if;
    end if;
