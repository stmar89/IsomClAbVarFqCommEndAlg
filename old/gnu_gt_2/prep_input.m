/*

    parallel --pipe --cat -N 100 "magma -b all:={} ./prep_input.m" < ../weil_poly_pRK_gt_1_noFp.txt

*/

    AttachSpec("../../depends.spec");
    AttachSpec("../../spec");
    file_out:="./input.m";
    PP<x>:=PolynomialRing(Integers());

    all1:=Split(Read(all));
    for cc in all1 do
        c:=[StringToInteger(c):c in Split(cc,"[ ,]")];
        g:=(#c-1) div 2;
        h:=PP!c;
        if IsSquarefree(h) then
            isog:=IsogenyClass(h:Check:=false);
            p:=CharacteristicFiniteField(isog);
            _,a:=IsPowerOf(FiniteField(isog),p);
            if a gt 2 then
                plE0,plE01,plE1:=PlacesOfQFAbove_p(isog);
                // look for nu such that gnu > 2 and sl(nu)=(0,1) 
                gnus_01:=[GCD(InertiaDegree(P),a): P in plE01];
                max:=Max(gnus_01);
                if max gt 2 then
                    printf "%o,%o\n",max,StripWhiteSpace(cc);
                    fprintf file_out,"%o\n",StripWhiteSpace(cc);
                end if;
            end if;
        end if;
    end for;
