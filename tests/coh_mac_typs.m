/*
    The experiments below, show that it is easy to find isogeny classes of dimension g,
    where R has an overorder S of CohenMacaulay type 2*g-1, that is the maximal possible value.
    It also sees that
        Max([CohenMacaulayType(S):S in OverOrders(R)]) eq Max([CohenMacaulayType(S):S in OverOrders(WR)]),
    that is, the extension \otimes W does not make this value grow. This is probably something one can prove...
    Something like
        - Every singular prime of WR is of the form P otimes W for a singular prime P of R, and 
        - dim_(R/P) OE/P*OE = dim_(WR/P otimes W) OA/(P otimes W)*OA
*/



    PP<x>:=PolynomialRing(Integers());
    SetAssertions(2);
    AttachSpec("~/AbVarFq/spec");
    AttachSpec("~/AlgEt/specMod");
    AttachSpec("~/AlgEt/specMtrx");
    AttachSpec("~/IsomClAbVarFqCommEndAlg/spec");
    all:=Split(Read("~/IsomClAbVarFqCommEndAlg/tests/weil_poly_sq_not_prime-ord-almord.txt"));
    g_old:=0;
    for s in all do
        cc:=[StringToInteger(c):c in Split(s,"[,]")];
        g:=(#cc-1) div 2;
        //if g gt g_old then g_old:=g; printf "%o",g; end if;
        q:=Round(cc[1]^(1/g));
        test,p,a:=IsPrimePower(q);
        if a le 5 and g ge 3 then
            h:=PP!cc;
            isog:=IsogenyClass(h);
            R:=ZFVOrder(isog);
            E:=DeligneAlgebra(isog);
            OE:=MaximalOrder(E);
            ss:=SingularPrimes(R);
            max_cm:=[];
            for P in ss do
                kP:=Index(R,P);
                OP:=Index(OE,OE!!P);
                Append(~max_cm,Ilog(kP,OP)-1);
            end for;
            max_cm_OE:=Max(max_cm);

            _,_,_,_,_,_,OA,_,WR:=DieudonneAlgebraCommEndAlg(isog);
            ss:=SingularPrimes(WR);
            max_cm:=[];
            for P in ss do
                kP:=Index(WR,P);
                OP:=Index(OA,OA!!P);
                Append(~max_cm,Ilog(kP,OP)-1);
            end for;
            max_cm_OA:=Max(max_cm);
            printf "a=%o,g=%o,max_cm_type_R=%o,max_cm_type_WR=%o\n",a,g,max_cm_OE,max_cm_OA;
        end if;
    end for;
