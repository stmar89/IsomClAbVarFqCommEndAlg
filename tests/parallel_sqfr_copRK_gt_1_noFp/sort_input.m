/*
    parallel -a ../weil_poly_sqfr_copRK_gt_1_noFp.txt --j 60 --joblog joblog --timeout 18000 magma -b cc:={} script.m
*/
    

    unsorted:="../weil_poly_sqfr_copRK_gt_1_noFp.txt";
    sorted:="weil_poly_sqfr_copRK_gt_1_noFp_sorted.txt";
    gas:=[];

    all:=[[StringToInteger(c):c in Split(d,"[ ,]")]:d in Split(Read(unsorted))];
    for cc in all do
        g:=(#cc-1) div 2;
        _,q:=IsPower(cc[1],g);
        _,p,a:=IsPrimePower(q);
        Append(~gas,g*a);
    end for;
    ParallelSort(~gas,~all);
    for i->cc in all do
        printf "%o\t%o\n",gas[i],StripWhiteSpace(Sprint(cc));
        fprintf sorted,"%o\n",StripWhiteSpace(Sprint((cc)));
    end for;
