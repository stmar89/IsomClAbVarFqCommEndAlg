/*
*/
    PP<x>:=PolynomialRing(Integers());
    all:=Split(Read("weil_poly_all.txt"));
    out_notFp:="weil_poly_pRK_gt_1_noFp.txt";
    out:="weil_poly_pRK_gt_1.txt";

    AttachSpec("../depends.spec");
    tot:=#all; perc:=0;
    for i->cc in all do
        if Truncate(i*100/tot) gt perc then perc+:=1; printf "%o%% ",perc; end if;
        c:=[StringToInteger(c):c in Split(cc,"[ ,]")];
        g:=(#c-1) div 2;
        if g ge 2 and not IsCoprime(c[1],c[g+1]) then // we skip ordinary
            h:=PP!c;
            if IsSquarefree(h) then
                isog:=IsogenyClass(h:Check:=false);
                f:=pRank(isog);
                if g-f gt 1 then //not almost ordinary
                    q:=FiniteField(isog);
                    fprintf out,"%o\n",StripWhiteSpace(cc); 
                    if not IsPrime(q) then
                        fprintf out_notFp,"%o\n",StripWhiteSpace(cc); 
                    end if;
                end if;
            end if;
        end if;
    end for;
