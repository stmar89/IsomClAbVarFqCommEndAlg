/*
    input is s:={}
*/

    sprint:=function(x)
        return StripWhiteSpace(Sprint(x));
    end function;

    SetAssertions(1);
    SetColumns(0);
    AttachSpec("~/AbVarFq/spec");
    AttachSpec("~/AlgEt/specMod");
    AttachSpec("~/AlgEt/specMtrx");
    AttachSpec("~/IsomClAbVarFqCommEndAlg/spec");
    file_out:="~/IsomClAbVarFqCommEndAlg/tests/bar_rho/output.m";

    PP<x>:=PolynomialRing(Integers());
    cc:=[StringToInteger(c):c in Split(s,"[,]")];
    h:=PP!cc;
    
    isog:=IsogenyClass(h);
    q:=FiniteField(isog);
    p:=CharacteristicFiniteField(isog);
    _,a:=IsPowerOf(q,p);
    nus0,nus01,nus1:=PlacesOfQFAbove_p(isog);
    _,_,_,_,A,_,OA,Delta_map,WR:=DieudonneAlgebraCommEndAlg(isog);
    R:=ZFVOrder(isog);
    E:=DeligneAlgebra(isog);
    pi:=PrimitiveElement(E);
    pps0:=[P:P in PrimesAbove(p*R)|pi in P and not q/pi in P];
    R_gnus_pps0:=[GCD(a,Ilog(p,Index(R,P))):P in pps0];
    PPs0,PPs01,PPs1:=PrimesOfSAbove_p(isog,WR);
    PP0_above_pp0:=[#[PP:PP in PPs0|forall{x:x in Generators(pps0[i])|Delta_map(x) in PP}]:i in [1..#pps0]];
    conj1:=#PPs01 eq 1;
    conj2:=forall{i:i in [1..#pps0]|PP0_above_pp0[i] eq R_gnus_pps0[i]};

    sl01:=[Slope(nu):nu in nus01];
    ParallelSort(~sl01,~nus01);
    data_nus:=[];
    for nu in nus0 do
        gnu:=GCD(InertiaDegree(nu),a);
        Append(~data_nus,Sprintf("[0,%o,f]",gnu));
    end for;
    
    conj3:=true;
    for inu->nu in nus01 do
        sl:=sl01[inu];
        gnu:=GCD(InertiaDegree(nu),a);
        conj_st:=nu eq ComplexConjugate(nu) select "t" else "f";
        if conj_st eq "f" then
            Append(~data_nus,Sprintf("[%o,%o,%o]",sl,gnu,conj_st));
        elif gnu eq 1 then
            Append(~data_nus,Sprintf("[%o,%o,%o,t]",sl,gnu,conj_st));
        else
            NUs:=PlacesOfDieudonneAlgebraSortedBySigmaAbovePlaceOfQF(isog,nu);
            bar_NUs:=[BarOnIdeal(isog,Q):Q in NUs];
            is_rho_id:=NUs[1] eq bar_NUs[1];
            if is_rho_id then
                conj3:=forall{i:i in [2..#NUs]|NUs[i] eq bar_NUs[i]};
            else
                conj3:=IsEven(gnu) and forall{i:i in [1..gnu div 2]|bar_NUs[i] eq NUs[(i+(gnu div 2))]}
                                   and forall{i:i in [(gnu div 2)+1..gnu]|bar_NUs[i] eq NUs[(i-(gnu div 2))]};
            end if;
            is_rho_id:=is_rho_id select "t" else "f";
            Append(~data_nus,Sprintf("[%o,%o,%o,%o]",sl,gnu,conj_st,is_rho_id));
        end if;
    end for;

    for nu in nus1 do
        gnu:=GCD(InertiaDegree(nu),a);
        Append(~data_nus,Sprintf("[1,%o,f]",gnu));
    end for;

    output:=Sprintf("a=%o:data_nus=%o:PP0_above_pp0=%o:R_gnus_pps0=%o:conj1=%o:conj2=%o:conj3=%o:s=%o",
            a,
            sprint(data_nus),
            sprint(PP0_above_pp0),
            sprint(R_gnus_pps0),
            conj1 select "t" else "f",
            conj2 select "t" else "f",
            conj3 select "t" else "f",
            sprint(s)
            );

    printf "%o\n",output;
    fprintf file_out,"%o\n",output;
