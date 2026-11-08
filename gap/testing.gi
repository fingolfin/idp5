#############################################################################
##
##  testing.gi                                              Idp5 package
##
##  Random isomorphic copies of groups and the test function
##  TestSmallGroupID_p5.
##
#############################################################################

BindGlobal( "p5id_random_spcgscopy", function(G)
    local new, max, C, M, Gpc, g, hom, Q;
    return PcGroupCode(RandomSpecialPcgsCoded(G), Size(G));
end );

BindGlobal( "p5id_random_pccopy", function(G)
    local new, max, C, M, Gpc, g, hom, Q;

    if not IsPcGroup(G) then return G; fi;
    new := [];
    if Size(G) = 1 then return G; fi;
    max := MaximalSubgroupClassReps(G);
    C   := G;
    M   := Random(max);
    while Size(M)>1 do
        hom    := NaturalHomomorphismByNormalSubgroup(C,M);
        Q      := Image(hom);
        repeat g := Random(Q); until not g = g^0;
        Add(new,PreImagesRepresentative(hom,g));
        C   := M;
        max := MaximalSubgroupClassReps(M);
        M   := Random(max);
    od;
    repeat g:= Random(C); until not g in M;
    Add(new, g);
    new := PcgsByPcSequenceNC(FamilyObj(One(G)),new);
    Assert(0, Product(RelativeOrders(new)) = Size(G));
    Gpc := PcGroupWithPcgs(new);
    return Gpc;
end );

BindGlobal( "p5id_random_pcgscopy", function(G)
    local pcg, n, p, new, i, j, g;

    if not IsPcGroup(G) then return G; fi;
    pcg := Pcgs(G);
    n   := Length(pcg);
    p   := RelativeOrders(pcg)[1];
    new := [];
    for i in [1..n] do
        g := pcg[i]^Random([1..p-1]);
        for j in [i+1..n] do
            g := g * pcg[j]^Random([0..p-1]);
        od;
        Add(new, g);
    od;
    return PcGroupWithPcgs(PcgsByPcSequenceNC(FamilyObj(One(G)), new));
end );



BindGlobal( "p5id_random_permcopy", function(G)
   local pcg, n, p, new, i, j, g;
   pcg := Image(IsomorphismPermGroup(G));
   repeat new := List([1..8],x->Random(pcg)); g := Group(new); until g=pcg;
   return g;
end );


#####################################################################################
##
## TestSmallGroupID_p5
##
## input:  a list lps of primes, the number nr of random copies to test, boolean testIso
##
## For every p in lps, every e in [1..5] and every i in [1..NumberSmallGroups(p^e)] we
## construct nr random copies of SmallGroup(p^e,i), compute the ID with IdSmallGroup,
## and check that it is correct. If testIso is true, then we also construct the isomorphism onto
## SmallGroup(p^5,i) with IsomorphismSmallGroup and verify that it is a bijective
## homomorphism; if the randomised search returns fail, then this is reported. For each
## copy the runtime of the ID and of the isomorphism is displayed. Displays report
## on 10 largest runtimes
##
InstallGlobalFunction( TestSmallGroupID_p5, function(lps, nr, testIso)
local idtimes, isotimes, wrong, failed, notiso, p, i, k, j, H, G, id, iso,
          t, tid, tiso, ok, x, y, l, report, e;

    idtimes  := [];
    isotimes := [];
    wrong    := [];
    failed   := [];
    notiso   := [];

    ## the ten largest entries of a list of triples [time, p, i]
    report := function(l, what)
        local av, s;
        if l = [] then return; fi;
        av := Sum(l, x -> x[1])/Length(l);
        Print("average time for ",what,": ",Int(av)," ms   (",Length(l)," tests)\n");
        s := ShallowCopy(l);
        SortBy(s, x -> -x[1]);
        Print("ten largest runtimes for ",what,":\n");
        for x in s{[1..Minimum(10,Length(s))]} do
            Print("   ",x[1]," ms   for SmallGroup(",x[2],"^5,",x[3],")\n");
        od;
    end;

    for p in lps do
        Print("------ start p = ",p,"\n");
        for e in [1,2,3,4] do
        for i in [1..NumberSmallGroups(p^e)] do
            H := SmallGroup(p^e,i);
            for k in [1..nr] do
                G   := p5id_random_pcgscopy(H);
               #G   := p5id_random_permcopy(H);
                t   := Runtime();
                id  := IdSmallGroup(G); ### new!
                tid := Runtime()-t;
                if not id = [p^e,i] then
                    Error("ID WRONG for ",[p^e,i],": got ",id,"\n");
                fi;
                if not testIso then
                    Print("ID [",p,"^",e,",",i,"] copy ",k,":  id ",tid," ms\n");
                else
                    t    := Runtime();
                    iso  := IsomorphismSmallGroup(G);
                    tiso := Runtime()-t;
                    if iso = fail then
                        Error("ID [",p,"^",e,",",i,"] copy ",k,":  id ",tid," ms,  iso ",tiso," ms,  iso failed\n");
                    else
                         iso := GroupHomomorphismByImages(Source(iso),Range(iso),
                                GeneratorsOfGroup(Source(iso)),
                                  List(List(GeneratorsOfGroup(Source(iso)),u->Image(iso,u))));
                        if not (not iso=fail and IsBijective(iso) and Source(iso) = G) then
                            Error("iso wrong  for ",[p^e,i],"\n");
                        fi;
                        Print("ID [",p,"^",e,",",i,"] copy ",k,":   id ",tid," ms,  iso ",tiso," ms\n");
                    fi;
                fi;
            od;
        od;
        od;
        for i in [1..NumberSmallGroups(p^5)] do
            H := SmallGroup(p^5,i);
            for k in [1..nr] do

                G   := p5id_random_pcgscopy(H);
                #G   := p5id_random_permcopy(H);

                t   := Runtime();
                id  := IdSmallGroup(G); ### new !!
                tid := Runtime()-t;
                Add(idtimes, [tid, p, i]);
                if not id = [p^5,i] then
                    Add(wrong, [p, i, id]);
                    Error("ID WRONG for ",[p^5,i],": got ",id,"\n");
                fi;
                if not testIso then
                    Print("ID [",p,"^5,",i,"] copy ",k,":  id ",tid," ms\n");
                else
                    t    := Runtime();
                    iso  := IsomorphismSmallGroup(G);
                    tiso := Runtime()-t;
                    Add(isotimes, [tiso, p, i]);
                    if iso = fail then
                        Add(failed, [p, i]);
                        Print("ID [",p,"^5,",i,"] copy ",k,":  id ",tid," ms,  iso ",tiso,
                              " ms,  random search failed\n");
                    else
                        iso := GroupHomomorphismByImages(Source(iso),Range(iso),
                                GeneratorsOfGroup(Source(iso)),
                                  List(List(GeneratorsOfGroup(Source(iso)),u->Image(iso,u))));
                         if not (not iso=fail and IsBijective(iso) and Source(iso) = G) then
                            Add(notiso, [p, i]);
                            Error("iso wrong  for ",[p^5,i],"\n");
                        fi;
                        Print("ID [",p,"^5,",i,"] copy ",k,":   id ",tid," ms,  iso ",tiso," ms\n");
                    fi;
                fi;
            od;
        od;
    od;

    Print("\n------ summary\n");
    report(idtimes, "ID");
    if testIso then report(isotimes, "iso"); fi;
    Print("wrong IDs: ",Length(wrong),"\n");
    Print("isomorphism search failed: ",Length(failed),"\n");
    Print("returned map not an isomorphism: ",Length(notiso),"\n");
    if not failed = [] then Print("   search failed for: ",failed,"\n"); fi;
    if not wrong = [] then Error("we have incorrect ids ",wrong); fi;
    if not notiso = [] then Error("we have incorrect isomorphisms ",notiso); fi;
    return rec(id := idtimes, iso := isotimes, wrong := wrong,
               failed := failed, notiso := notiso);
end );
