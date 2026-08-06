
    PP<x>:=PolynomialRing(Integers());
    AttachSpec("~/AbVarFq/spec");
    AttachSpec("~/AlgEt/specMod");
    AttachSpec("~/AlgEt/specMtrx");
    AttachSpec("~/IsomClAbVarFqCommEndAlg/spec");
    lines:=Split(Read("~/IsomClAbVarFqCommEndAlg/tests/bar_rho/output.m"));
    /*
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
     */
     function ReplaceAll(s, pattern, replacement)
        res := "";
        p := Position(s, pattern);

        while p gt 0 do
            // Append the text up to the pattern + the replacement
            res := res cat s[1 .. p-1] cat replacement;
            // Advance past the matched pattern
            s := s[p + #pattern .. #s];
            p := Position(s, pattern);
        end while;

        // Append any remaining trailing characters
    return res cat s;
    end function;
    conj_pair:=AssociativeArray(:Default:=0);
    rho_id:=AssociativeArray(:Default:=0);
    rho_notid:=AssociativeArray(:Default:=0);
     for line in lines do
         all:=Split(line,":");
         a:=StringToInteger(Split(all[1],"=")[2]);
         data_nus:=Split(all[2],"=")[2];
         data_nus:=ReplaceAll(data_nus,"[","<");
         data_nus:=ReplaceAll(data_nus,"]",">");
         data_nus:=ReplaceAll(data_nus,"t","true");
         data_nus:=ReplaceAll(data_nus,"f","false");
         data_nus:=eval(data_nus);
         for nu in data_nus do
             if not nu[3] then
                 conj_pair[a]:=Max(conj_pair[a],nu[2]);
             elif nu[4] then
                rho_id[a]:=Max(rho_id[a],nu[2]);
             else
                rho_notid[a]:=Max(rho_notid[a],nu[2]);
             end if;
          end for;
     end for;
     for a->M in conj_pair do
         a,M;
     end for;
     for a->M in rho_id do
         a,M;
     end for;
     for a->M in rho_notid do
         a,M;
     end for;

