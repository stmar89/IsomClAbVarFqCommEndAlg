    
    SetAssertions(2);

    AttachSpec("~/AbVarFq/spec");
    //AttachSpec("~/AlgEt/spec"); // this spec file in is magma since 2.29
    AttachSpec("~/AlgEt/specMod");
    AttachSpec("~/AlgEt/specMtrx");
    AttachSpec("~/IsomClAbVarFqCommEndAlg/spec");

    function Base26Encode(n)
            alphabet := "abcdefghijklmnopqrstuvwxyz";
            s := alphabet[1 + n mod 26]; n := ExactQuotient(n-(n mod 26),26);
            while n gt 0 do
                    s := alphabet[1 + n mod 26] cat s; n := ExactQuotient(n-(n mod 26),26);
            end while;
            return s;
    end function;

    function IsogenyLabel(f)
    // returns the LMFDB label of the isogeny class determined by a Weil polynomial f.
        g:=Degree(f) div 2;
        q:=Integers() ! (Coefficients(f)[1]^(2/Degree(f)));
        str1:=Reverse(Prune(Coefficients(f)))[1..g];
        str2:="";
        for a in str1 do
            if a lt 0 then
                str2:=str2 cat "a" cat Base26Encode(-a) cat "_";
                else
                str2:=str2 cat Base26Encode(a) cat "_";
            end if;
        end for;
        str2:=Prune(str2);
        isog_label:=Sprintf("%o.%o.",g,q) cat str2;
        return isog_label;
    end function;

    PP<x>:=PolynomialRing(Integers());
    input:=[
    (x^2-2*x+4)*(x^2+2*x+4),
    x^8 - 6*x^7 + 18*x^6 - 36*x^5 + 68*x^4 - 144*x^3 + 288*x^2 - 384*x + 256,
    x^6 - x^5 - 3*x^4 + 45*x^3 - 27*x^2 - 81*x + 729,
    x^8+x^7+x^6+4*x^5-4*x^4+16*x^3+16*x^2+64*x + 256,
    x^6 + 11*x^5 + 60*x^4 + 208*x^3 + 480*x^2 + 704*x + 512
    ];
    for h in input do
        isog:=IsogenyClass(h);
        p:=CharacteristicFiniteField(isog);
        plE0,plE01,plE1:=PlacesOfQFAbove_p(isog);
        plE:=plE01;;
        plA:=Seqset(&cat[PlacesOfDieudonneAlgebraAbovePlaceOfQF(isog,nu):nu in plE]); 
        // We compute the W'_R-isomorphim classes of W'_R-ideals.
        _,_,_,_,_,_,OA,_,WR:=DieudonneAlgebraCommEndAlg(isog);
        k:=Valuation(Index(OA,WR),p);
        WR_plE:=Order( ZBasis(WR) cat ZBasis(OA!!&*[ P^(k*RamificationIndex(P)) : P in plA ]));
        oo:=OverOrders(WR_plE);
        for S in oo do
            pp_ff:=Seqset(PrimesAbove(OA!!Conductor(S)));
            assert pp_ff subset plA;
            #plA,#pp_ff;
        end for;
    end for;
