/*

    This parallel script takes as input a big list of squarefree isogeny classes over non-prime fields of dimension g 
    with p-rank < g-1 (so neither ordinary nor almost-ordinary) with a local-local place with g_nu>2.
    For each such class it outputs the number of isomorphism classes and timings.

    parallel --joblog joblog --timeout 600 -a input.m magma -b cc:={} ./iso_script.m 

*/

    AttachSpec("../../depends.spec");
    AttachSpec("../../spec");
    file_out:="./iso_timings.m";
    PP<x>:=PolynomialRing(Integers());

    c:=[StringToInteger(c):c in Split(cc,"[ ,]")];
    h:=PP!c;
    isog:=IsogenyClass(h:Check:=false);
    t0:=Cputime();
    iso:=IsomorphismClasses(isog);
    t1:=Round(Cputime(t0));

    printf "%o isom. cl. in %o secs",#iso,t1;
    fprintf file_out,"%o isom. cl. in %o secs",#iso,t1;

