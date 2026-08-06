
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
     function ReplaceAll(s0, patterns, replacements)
        s:=s0;
        for i in [1..#patterns] do
            pattern:=patterns[i];
            replacement:=replacements[i];
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
            s:=res cat s;
        end for;
        return s;
    end function;

    conj_pair:=AssociativeArray(:Default:=0);
    rho_id:=AssociativeArray(:Default:=0);
    rho_notid:=AssociativeArray(:Default:=0);
    max_conj_pair:=AssociativeArray(:Default:=[]);
    max_rho_id:=AssociativeArray(:Default:=[]);
    max_rho_notid:=AssociativeArray(:Default:=[]);
    for line in lines do
         all:=Split(line,":");
         a:=StringToInteger(Split(all[1],"=")[2]);
         cc:=Split(all[#all],"=")[2];
         data_nus:=Split(all[2],"=")[2];
         data_nus:=ReplaceAll(data_nus,["[","]","t","f"],["<",">","true","false"]);
         data_nus:=eval(data_nus);
         for nu in data_nus do
             if not nu[3] then
                 if nu[2] gt conj_pair[a] then
                     conj_pair[a]:=nu[2];
                     max_conj_pair[a]:={@ cc @}; // we reset it
                 elif nu[2] eq conj_pair[a] then
                     Include(~max_conj_pair[a],cc);
                 end if;
             elif nu[4] then
                 if nu[2] gt rho_id[a] then
                     rho_id[a]:=nu[2];
                     max_rho_id[a]:={@ cc @}; // we reset it
                 elif nu[2] eq rho_id[a] then
                     Include(~max_rho_id[a],cc);
                 end if;
             else
                 if nu[2] gt rho_notid[a] then
                     rho_notid[a]:=nu[2];
                     max_rho_notid[a]:={@ cc @}; // we reset it
                 elif nu[2] eq rho_notid[a] then
                     Include(~max_rho_notid[a],cc);
                 end if;
             end if;
          end for;
     end for;
     printf "conj_pair\n";
     for a->M in conj_pair do
         a,M,#max_conj_pair[a];
     end for;
     printf "rho_id\n";
     for a->M in rho_id do
         a,M,#max_rho_id[a];
     end for;
     printf "rho_notid\n";
     for a->M in rho_notid do
         a,M,#max_rho_notid[a];
     end for;

     // We take the maximal g_nus and break even by taking th minimal a
     // For rho_id we get at most only g_nu=2 :-( not very interesting.
     for cc in max_conj_pair[3] do
         fprintf "~/IsomClAbVarFqCommEndAlg/tests/bar_rho/conj_pair_a_3_gnu_3.txt","%o\n",cc;
     end for;
     for cc in max_rho_notid[4] do
         fprintf "~/IsomClAbVarFqCommEndAlg/tests/bar_rho/rho_notid_a_4_gnu_4.txt","%o\n",cc;
     end for;
     
