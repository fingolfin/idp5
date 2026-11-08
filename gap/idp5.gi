#############################################################################
##
##  idp5.gi                                                 Idp5 package
##
##  Identification of the groups of order p^5: the families with constant
##  and with non-constant log-sequence profiles, and the main identification
##  function p5id_Idp5Group for groups of order dividing p^5.
##
#############################################################################

#####################################################################################
#####################################################################################
#####################################################################################
#####################################################################################
#####################################################################################
##
##
## Now do the constant classes for p^5
##
##


BindGlobal( "p5id_profiles", function(G)
local lcs, lps;

   if Size(G) = 1 then return [[0],[0]]; fi;
   lcs := List(Filtered(LowerCentralSeries(G),y-> Size(y)>1),x->Collected(FactorsInt(Size(x)))[1][2]);
   Add(lcs,0);
   lps := List(Filtered(PCentralSeries(G),y-> Size(y)>1),x->Collected(FactorsInt(Size(x)))[1][2]);
   Add(lps,0);
   return [lps,lcs];
end );



#####################################################################################
## Identification function for groups G of size p^5 that lie in a log-sequence family
## of constant size
## input:  group G and ls = [lps, lcs]
## output: group ID
##
BindGlobal( "p5id_idp5_constant", function(G,ls)
   local p, iso, getspecialmax1, getspecialmax2, getspecialfact, singleton, constant,
   pos, startid, nr, e, U, c, els, d, hom, Q, idp4, gen, DB, z, g, C, h, mat, myf, id,
   a, b, i, done, aa, bb, dd, ee, cc, frs, u, gz, w, snd, v;

   p := PrimePGroup(G);
   iso := fail;

   ## helping function for G20, G21, G25, G25
   ## construct ID of preimage of nonab max in G/G'\cap G^p
   getspecialmax1 := function(H, abl)
      local F, hom, gens, HQ, iso, id;
      F   := Intersection(DerivedSubgroup(H),Agemo(H,PrimePGroup(H)));
      hom := NaturalHomomorphismByNormalSubgroupNC(H,F);
      HQ  := Image(hom);
      iso := p5id_p4IsoStandard(HQ).iso;
      if abl then
         gens := GeneratorsOfGroup(Image(iso)){[2,3,4]};
      else
         gens := GeneratorsOfGroup(Image(iso)){[1,2,4]};
      fi;
      gens := List(gens,x-> PreImagesRepresentative(hom,PreImagesRepresentative(iso,x)));
      Add(gens,MinimalGeneratingSet(F)[1]);
      HQ  := Subgroup(H,gens);
      id := p5id_p4IsoStandard(HQ);
      if not abl or id.id[2] = 14 then
         return id;
      elif id.id[2] <> 14 then
         gens := GeneratorsOfGroup(Image(iso)){[1,3,4]};
         gens := List(gens,x-> PreImagesRepresentative(hom,PreImagesRepresentative(iso,x)));
         Add(gens,MinimalGeneratingSet(F)[1]);
         HQ  := Subgroup(H,gens);
         id := p5id_p4IsoStandard(HQ);
         return id;
      fi;
   end;

   getspecialmax2 := function(H)
      local p, F, hom, HQ, iso, gens, id;
      p := PrimePGroup(H);
      F   := Intersection(DerivedSubgroup(H), Center(H));
      hom := NaturalHomomorphismByNormalSubgroupNC(H,F);
      HQ  := Image(hom);
      iso := p5id_p4IsoStandard(HQ).iso;
      gens := GeneratorsOfGroup(Image(iso)){[2,3,4]};
      gens := List(gens,x -> PreImagesRepresentative(hom,PreImagesRepresentative(iso,x)));
      gens:= Concatenation(gens,MinimalGeneratingSet(F));
      HQ  := Subgroup(H,gens);
      id := p5id_p4IsoStandard(HQ);
      return id;
   end;

   getspecialfact := function(H)
      local p, C, gens, i, id;
      p := PrimePGroup(H);
      C   := Center(H);
      gens := SmallGeneratingSet(C);
      id := p5id_p4IsoStandard(H/Subgroup(H, [gens[1]]));
      if id.id = [p^4, 3] then
         id := p5id_p4IsoStandard(H/Subgroup(H, [gens[2]]));
      fi;
      return id;
   end;

   ### the ls where the families are singletons
   singleton := [ [[5, 0], [5, 0]], [[5, 1, 0], [5, 0]], [[5, 2, 0], [5, 0]],
                  [[5, 2, 1, 0], [5, 0]], [[5, 3, 0], [5, 1, 0]],
                  [[5, 3, 1, 0], [5, 0]], [[5, 3, 2, 1, 0], [5, 0]],
                  [[5, 3, 2, 1, 0], [5, 1, 0]], [[5, 4, 3, 2, 1, 0], [5, 0]] ];

   ### the ls where the families are constant but not singletons
   constant :=  [ [[5,1,0], [5,1,0], 5], [[5,2,0],[5,1,0], 5],
                  [[5,2,1,0],[5,1,0], 2], [[5,2,1,0],[5,2,1,0], 10],
                  [[5,3,1,0], [5,1,0], 3], [[5,3,1,0], [5,2,1,0], 9]];

   pos := Position(singleton,ls);
   if not pos=fail then return rec(id:=[1,2,8,14,27,28,41,42,43][pos],iso:=fail); fi;

   pos := Position(List(constant,u->u{[1,2]}),ls);
   if pos = fail then Error("should not happen"); fi;
   startid  := [2,8,14,16,28,31][pos]; #add position of group to this

   if pos = 1 then
      nr := Position([[p,3], [p,1], [p^2,3], [p^2,2], [p^2,1]],[Exponent(G),RankPGroup(Centre(G))]);

      if nr = 4 and false then #####type 68
         #68  --> our G_6 (Exponent (p^2, RankPGroup(Centre(G)) = (p^2,2)(
         # NEED b^a=be, c^p=e
         e := MinimalGeneratingSet(Agemo(G,p))[1];
         U := Subgroup(G,[e]);
         c := First(Pcgs(Centre(G)),x->x^p in U);
         e := c^p;
         U := Subgroup(G,[c]);
         els := List(Pcgs(Omega(Center(G),p)),x->x);
         Add(els,els[1]*els[2]);
         d := First(els,x-> p5id_p4IsoStandard(G/Subgroup(G,[x])).id=[p^4,14]);
         hom := NaturalHomomorphismByNormalSubgroup(G,Subgroup(G,[d]));
         Q   := Image(hom);
         idp4 := p5id_p4IsoStandard(Q);
         if not idp4.id = [p^4,14] then Error("wrong id quotient"); fi;
         iso := idp4.iso;
         gen := List(GeneratorsOfGroup(Image(iso)),x->PreImagesRepresentative(iso,x));
         gen := List(gen,x->PreImagesRepresentative(hom,x));
         DB  := SmallGroup(p^5,IdSmallGroupFromType_p5(p,68));
         iso := GroupHomomorphismByImagesNC(G,DB,[gen[1],gen[2],gen[3],d,gen[4]],Pcgs(DB));
         if iso=fail then Error("iso false");  fi;
      fi;

      if nr = fail then Error("should not happen"); fi;
      return rec(id:=startid + nr, iso:=iso);
   fi;

    if pos = 2 then
      z  := Centre(G);
      nr := Position([[p^2,p],[p,p],[p,p^2],[p^2,p^2]], [Exponent(z),Size(Agemo(G,p))]);

      if nr = fail then Error("should not happen"); fi;

      if nr in [1,2,3] then return rec(id:=startid + nr, iso:=fail); fi;

      startid := startid+3;
      #now distinguish the two groups C_p \ltimes (C_{p^2} x C_{p^2})

      nr := Position([[p^4, 11], [p^4, 13]],
            p5id_p4IsoStandard(G/Agemo(Center(G),p)).id);
      return rec(id:=startid+nr,iso:=fail);

      g := First(GeneratorsOfGroup(G),x->Order(x)=p^2);
   fi;

   if pos = 3 then
      if Exponent(Centre(G))=p^3 then
         return rec(id:=startid + 1, iso:=fail);
      else
         return rec(id:=startid + 2, iso:=fail);
      fi;
   fi;

   myf :=2;
   if pos = 4 then
      if Size(Centre(G))=p^2 then ##types 54,55,56,57,58
         if IsCyclic(Centre(G)) then return rec(id:=startid + 2, iso:=fail); fi; #55
         if Size(Agemo(G,p))=1 then return rec(id:=startid + 1, iso:=fail); fi;  #54
         if IsElementaryAbelian(Centraliser(G,DerivedSubgroup(G))) then
                return rec(id:=startid + 3, iso:=fail); #56
         fi;

         ## now it remains to differntiate 57 and 58: these have different actions (use smaller group ID?)
         ## 57 has (p^4,10) but no (p^4,9), and 58 is vice versa
         id := getspecialmax1(G, false);
         if id.id = [p^4,10] then return rec(id:=startid + 4, iso:=fail);
         elif id.id=[p^4,9] then return rec(id:=startid + 5, iso:=fail);
         else Error("arg!"); fi;

      else #center=p and 59,60,61,62,63
         if Size(Agemo(G,p))=1 then return rec(id:=startid + 6, iso:=fail); fi; #59
         if Exponent(Centraliser(G,DerivedSubgroup(G)))=p then
            return rec(id:=startid + 8, iso:=fail); #61
         fi;

         ## now it remains to differntiate 62, 63: these have different actions (use smaller group ID?)
         id := getspecialmax1(G, true);
         if id.id = [p^4,14] then return rec(id:=startid + 7, iso:=fail); fi; #60

         ### 62 has (p^4,10) but no (p^4,9), and 63 is vice versa
         id := getspecialmax1(G, false);

         if id.id = [p^4,10] then return rec(id:=startid + 9, iso:=fail);
         elif id.id = [p^4,9] then return rec(id:=startid + 10, iso:=fail);
         else Error("arg"); fi;

      fi;
   fi;

   if pos = 5 then
      nr := Position([[p^3,p^2],[p^2,p^3],[p^3,p^3]], [Size(Agemo(G,p)),Exponent(G/DerivedSubgroup(G))]);
      return rec(id:=startid + nr, iso:=fail);
   fi;

   if pos = 6 then
      if AbelianInvariants(Agemo(G, p)) = [p] then
         id := getspecialmax2(G);
         if id.id = [p^4, 15] then
            return rec(id:=startid+1,iso:=fail); #16
         elif id.id = [p^4, 12] then
            return rec(id:=startid + 5,iso:=fail); #20
         fi;

      elif AbelianInvariants(Agemo(G,p)) = [p,p] then
         id := getspecialmax2(G);
         if id.id = [p^4, 13] then
            return  rec(id:=startid+6,iso:=fail); #21
         fi;

         id := getspecialfact(G);
            if id.id = [p^4,9] then
               return rec(id:=33,iso:=fail); #17
            elif id.id = [p^4,10] then
               return rec(id:=34,iso:=fail); #18
            fi;

      elif AbelianInvariants(Agemo(G,p)) = [p,p^2] then
         return rec(id:=startid+9,iso:=fail); #24

      elif AbelianInvariants(Agemo(G,p)) = [p^2] then
         id := getspecialmax2(G);
         if id.id = [p^4, 11] then
            return rec(id:=startid+4,iso:=fail); #19
         fi;

         #now it remains to distinguish 22 and 23
         U   := Agemo(Centre(G),p);
         gz   := MinimalGeneratingSet(Centre(G))[1];
         hom := NaturalHomomorphismByNormalSubgroup(G,U);
         iso := p5id_p4IsoStandard(Image(hom)).iso;

         ##Display("start auts");
         ##for alp in AutomorphismGroup(Image(iso)) do

         gen := List(GeneratorsOfGroup(Image(iso)),x->PreImagesRepresentative(iso,x));
         gen := List(gen,x->PreImagesRepresentative(hom,x));
         w   := gen[2]^p;
         if not w=w^0 then
            i:=First([1..p^2-1],x->(gz^(p*x)=w)); gen[2] := gen[2]*gz^-i;
         fi;
         w   := gen[3]^p;
         if not w=w^0 then
            i:=First([1..p^2-1],x->(gz^(p*x)=w)); gen[3] := gen[3]*gz^-i;
         fi;
         ## sanity check
         if not Order(gen[2])=p or not Order(gen[3])=p or not Order(gen[1])=p^3
             or not gen[3]^-1*Comm(gen[2],gen[1]) in U or not Comm(gen[3],gen[1]) in U or not Comm(gen[3],gen[2]) in U then
            Error("should not have happened");
         fi;

         b := gen[2];
         c := gen[3];
         a := gen[1];
         if Comm(c,a)=One(G) then a:=a*b; fi;
         d := a^p; e:= d^p;

         done := false;
         i    := 0;
         aa   := One(G);
         while not done do
            i  := i+1;
            aa := aa*a; ##a^i
            bb := b;
            dd := aa^p;
            ee := dd^p;
            cc := Comm(bb,aa);
            frs := Comm(cc,aa);
            snd := Comm(cc,bb);
            u  := First([1..p-1],x-> frs=ee^x);
            v  := First([1..p-1],x-> snd=ee^x);
            if u=v then done := true; a:=aa; b:=bb; c:=cc; d:=dd; e:=ee; fi;
            if i > p^3 then Error("mhmm... this should not have happened"); fi;
         od;

         if (u*One(GF(p)))^((p-1)/2)=One(GF(p)) then
            return rec(id:=38,iso:=fail);
         else
            return rec(id:=39,iso:=fail);
         fi;
      fi;
   fi;

   return true;
end );



#####################################################################################
#####################################################################################
#####################################################################################
#####################################################################################
#####################################################################################
##
##
## Now do the non-constant classes for p^5
##
##



#####################################################################################
## Creates the p-cover for a given prime and family of groups
## input:  prime p, integer fam (16, 17, 18)
## output: the p-cover for the respective family
##
BindGlobal( "p5id_getPCover", function(p, fam)
    local F, gens, R, i, j;

    if fam = 6 then
        F := FreeGroup(9);
        gens := GeneratorsOfGroup(F);

        R := [F.1^p/F.4, F.2^p/F.5, F.3^p/F.6,
              Comm(F.2,F.1)/F.7, Comm(F.3,F.1)/F.8, Comm(F.3,F.2)/F.9];

        for i in [4..9] do Add(R, gens[i]^p); od;

        for i in [4..9] do
            for j in [1..i-1] do
                Add(R, Comm(gens[i], gens[j]));
            od;
        od;

    elif fam = 14 then
        F := FreeGroup(7);
        gens := GeneratorsOfGroup(F);

        R := [F.1^p/F.4, F.2^p/F.5,
              Comm(F.2,F.1)/F.3, Comm(F.3,F.1)/F.6, Comm(F.3,F.2)/F.7];

        for i in [3..7] do Add(R, gens[i]^p); od;

        for i in [4..7] do
            for j in [1..i-1] do
                Add(R, Comm(gens[i], gens[j]));
            od;
        od;

    elif fam = 17 then
        F := FreeGroup(8);
        gens := GeneratorsOfGroup(F);

        R := [F.1^p/F.5, F.2^p/F.6, Comm(F.2,F.1)/F.3,
            Comm(F.3,F.1)/F.4, Comm(F.3,F.2)/F.7, Comm(F.4, F.1)/F.8,
            Comm(F.4, F.2), Comm(F.4, F.3)];

        for i in [3..8] do Add(R, gens[i]^p); od;

        for i in [5..8] do
            for j in [1..i-1] do
                Add(R, Comm(gens[i], gens[j]));
            od;
        od;

    else
        Error("Only implemented for families 6, 14 and 17");
    fi;

   return PcGroupFpGroup(F/R);
end );



#####################################################################################
## Returns a matrix that operates on the allowable subspaces of family
## input:  prime p, integer fam (16, 17, 18), either element of GL(3,p) (fam=16),
##                  elementof of GL(2,p) (fam=17) or [x,y,z] with 1<=x,y<p, 0<=z<p
## output: matrix
##
BindGlobal( "p5id_famMats", function(p, fam, arg)
    local m, M, v;
    if fam = 6 then
        m := arg;
        if Rank(m) < 3 then Info(InfoIdp5, 1, "p5id_famMats: singular matrix"); fi;
        M := ZeroMatrix(6, 6, m);
        M{[1..3]}{[1..3]} := m;
        M[4][4] := m[1][1]*m[2][2]-m[1][2]*m[2][1];
        M[4][5] := m[1][1]*m[2][3]-m[1][3]*m[2][1];
        M[4][6] := m[1][2]*m[2][3]-m[1][3]*m[2][2];
        M[5][4] := m[1][1]*m[3][2]-m[1][2]*m[3][1];
        M[5][5] := m[1][1]*m[3][3]-m[1][3]*m[3][1];
        M[5][6] := m[1][2]*m[3][3]-m[1][3]*m[3][2];
        M[6][4] := m[2][1]*m[3][2]-m[2][2]*m[3][1];
        M[6][5] := m[2][1]*m[3][3]-m[2][3]*m[3][1];
        M[6][6] := m[2][2]*m[3][3]-m[2][3]*m[3][2];

    elif fam = 14 then
        m := arg;
        M := ZeroMatrix(4, 4, m);
        M{[1,2]}{[1,2]} := m;
        M{[3,4]}{[3,4]} := DeterminantMat(m)*m;

    elif fam = 17 then
        v := arg*Z(p)^0;
        if v[1]*Z(p) = 0*Z(p) or v[2]*Z(p) = 0*Z(p) then
            Error("v[1] and v[2] must be inversable");
        fi;
        M := ZeroMatrix(GF(p), 4, 4);
        M[1][1] := v[1];
        M[2][2] := v[2];
        M[1][2] := v[3];
        M[3][3] := M[1][1]*M[2][2]^2;
        M[4][4] := M[1][1]^3*M[2][2];
    fi;

    return M*Z(p)^0;
end );



#####################################################################################
## Determines the type of the group corresponding to the provided dual base of an
## allowed subpace of family 16
## input: a base of the dual of an allowed subspace. Must be in RREF
## output: the corresponding type, either a single integer or a list of two integers
##
BindGlobal( "p5id_fam6id", function(base)
    local p, r, trans, type, ps, can, eig, TD, k, B;

    p := Characteristic(base);
    r := RankMat(base{[1,2]}{[1..3]});
    trans := IdentityMatrix(GF(p), 6);
    can := base;

    if r = 0 then
        type := 34;

    elif r = 1 then

        ps := Last([1..3], i -> base[1][i] <> Zero(GF(p)));
        if ps = 1 then
            trans := p5id_famMats(p, 6, ([[0,1,0],[0,0,1], can[1]{[1..3]}]*Z(p)^0)^-1);
        elif ps = 2 then
            trans := p5id_famMats(p, 6, ([[1,0,0],[0,0,1], can[1]{[1..3]}]*Z(p)^0)^-1);
        else
            trans := p5id_famMats(p, 6, ([[1,0,0],[0,1,0], can[1]{[1..3]}]*Z(p)^0)^-1);
        fi;

        can := RREF(base*trans);

        if can[1][4] <> 0*Z(p)^0 then
            type := 39;

        elif can[2][4] <> 0*Z(p)^0 then
            type := 36;

        elif can{[1,2]}[4] = [0,0]*Z(p)^0 then
            type := 38;
        fi;

    elif r = 2 then

        ps := First(Tuples([1..3],2), t -> base[1][t[1]] <> 0*Z(p) and base[2][t[2]] <> 0*Z(p));
        if not 1 in ps then
            trans := p5id_famMats(p, 6, [[1,0,0]*Z(p)^0, can[1]{[1..3]}, can[2]{[1..3]}]^-1);
        elif not 2 in ps then
            trans := p5id_famMats(p, 6, [[0,1,0]*Z(p)^0, can[1]{[1..3]}, can[2]{[1..3]}]^-1);
        else
            trans := p5id_famMats(p, 6, [[0,0,1]*Z(p)^0, can[1]{[1..3]}, can[2]{[1..3]}]^-1);
        fi;
        can := RREF(base * trans);

        eig := Eigenvalues(GF(p), can{[1,2]}{[4,5]});

        if Size(eig) = 0 then
            TD := TraceMat(can{[1,2]}{[4,5]})^2/DeterminantMat(can{[1,2]}{[4,5]});
            if TD = 0*Z(p) then
               type := 49;
            else
               k := (1+DLog(Z(p), Z(p)^0-4*Z(p)^0/(TD)))/2;
               type := [50, k];
            fi;

        elif Size(eig) = 1 then
            if eig[1] = 0*Z(p) then
               type := 41;
            elif can{[1,2]}{[4,5]} = can[1][4]*[[1,0],[0,1]] then
               type := 44;
            else
               type := 46;
            fi;

        else
            if 0*Z(p) in eig then
               type := 42;
            else
               k := DLog(Z(p), eig[2]/eig[1]);
               if k > (p-1)/2 then k := -k mod (p-1); fi;
               type := [48, k];
            fi;
        fi;
    else
        Error("No mathcing type found in family (6)");
    fi;
    return type;
end );



#####################################################################################
## Calculates the transversal element (a matrix) that maps the provided base to the
## canonical dual base of the given type from family 16
## input: the type (either an integer or a pair of integers) and the starting base
## output: a matrix
##
BindGlobal( "p5id_fam6trans", function(type, base)
    local p, trans, x, y, ps, can, c, d, ab, z, pot;

    p := Characteristic(base);
    trans := IdentityMatrix(GF(p), 6);

    if type = 34 then

        if base{[1,2]}{[4,5,6]} = [[0,1,0],[0,0,1]]*Z(p)^0 then
            trans := trans;

        elif base{[1,2]}{[4,5]} = [[1,0],[0,1]]*Z(p)^0 then
            x := base[1][6];
            y := base[2][6];
            if x <> 0*Z(p) and y <> 0*Z(p) then
                trans := [[0,x,0,0,0,0],[1,y,0,0,0,0],[-x^-1,-y/x,1,0,0,0],
                    [0,0,0,-x,0,0],[0,0,0,1,0,x],[0,0,0,0,1,y]] * Z(p)^0;
            elif x <> 0*Z(p) then
                trans := [[0,x,0,0,0,0], [1,0,0,0,0,0], [-x^-1,0,1,0,0,0],
                    [0,0,0,-x,0,0], [0,0,0,1,0,x], [0,0,0,0,1,0]] * Z(p)^0;
            elif y <> 0*Z(p) then
                trans := [[0,-y,0,0,0,0], [0,0,-y,0,0,0], [y^-1,1,0,0,0,0],
                    [0,0,0,0,0,y^2], [0,0,0,1,0,0], [0,0,0,0,1,y]] * Z(p)^0;
            else
                trans := [[0,1,0,0,0,0], [0,0,1,0,0,0], [-1,0,0,0,0,0],
                    [0,0,0,0,0,1], [0,0,0,1,0,0], [0,0,0,0,1,0]] * Z(p)^0;
            fi;

        elif base{[1,2]}{[4,6]} = [[1,0],[0,1]]*Z(p)^0 then
            x := base[1][5];
            if x <> 0*Z(p) then
                trans := [[1,0,0,0,0,0], [0,x^-1,0,0,0,0], [0,1,x,0,0,0],
                    [0,0,0,x^-1,0,0], [0,0,0,1,x,0], [0,0,0,0,0,1]] * Z(p)^0;
            else
                trans := [[1,0,0,0,0,0], [0,0,-1,0,0,0], [0,1,0,0,0,0],
                    [0,0,0,0,-1,0], [0,0,0,1,0,0], [0,0,0,0,0,1]] * Z(p)^0;
            fi;
        else
            Error("This should not be possible");
        fi;

        trans := trans^-1;

    elif type in [36, 38, 39] then

        ps := Last([1..3], i -> base[1][i] <> Zero(GF(p)));
        if ps = 1 then
            trans := p5id_famMats(p, 6, ([[0,1,0],[0,0,1], can[1]{[1..3]}]*Z(p)^0)^-1);
        elif ps = 2 then
            trans := p5id_famMats(p, 6, ([[1,0,0],[0,0,1], can[1]{[1..3]}]*Z(p)^0)^-1);
        else
            trans := p5id_famMats(p, 6, ([[1,0,0],[0,1,0], can[1]{[1..3]}]*Z(p)^0)^-1);
        fi;

        can := RREF(base*trans);

        if type = 36 then
            c := can[1][5];
            d := can[1][6];

            ab := Filtered(Tuples([0..p-1]*Z(p)^0, 2), t -> t[1]*d-t[2]*c = can[2][4]);

            for y in [0..p-1]*Z(p)^0 do
                for z in [0..p-1]*Z(p)^0 do
                    pot := Filtered(ab, t -> t[1]*y-c*z = can[2][5]);
                    if Size(pot) = 0 then continue; fi;

                    pot := Filtered(pot, t -> t[2]*y-d*z = can[2][6]);
                    if Size(pot) <> 0 then
                        ab := pot;
                        break;
                    fi;
                od;
            od;

            trans := trans * p5id_famMats(p, 6, [[ab[1][1], ab[1][2], z],
                        [c, d, y], [0,0,1]]*Z(p)^0)^-1;

        elif type = 38 then
            trans := trans * p5id_famMats(p, 6, [[can[2][5], can[2][6], 0],
                                [can[1][5], can[1][6], 0], [0,0,1]]*Z(p)^0)^-1;
        elif type = 39 then
            c := Z(p)^0;
            d := can[2][6];

            ab := Filtered(Tuples([0..p-1]*Z(p)^0, 2), t -> t[1]*d-t[2]*c = can[1][4]);

            for y in [0..p-1]*Z(p)^0 do
                for z in [0..p-1]*Z(p)^0 do
                    pot := Filtered(ab, t -> t[1]*y-c*z = can[1][5]);
                    if Size(pot) = 0 then continue; fi;

                    pot := Filtered(pot, t -> t[2]*y-d*z = can[1][6]);
                    if Size(pot) <> 0 then
                        ab := pot;
                        break;
                    fi;
                od;
            od;

            trans := List(ab, t-> trans * p5id_famMats(p, 6, [[t[1], t[2], z],
                            [c, d, y], [0,0,1]]*Z(p)^0)^-1);
        else
            Error();
        fi;

    else
        ps := First(Tuples([1..3],2), t -> [base[1][t[1]], base[2][t[2]]] <> [0, 0] * Z(p));

        if not 1 in ps then
            trans := p5id_famMats(p, 6, [[1,0,0]*Z(p)^0, can[1]{[1..3]}, can[2]{[1..3]}]^-1);
        elif not 2 in ps then
            trans := p5id_famMats(p, 6, [[0,1,0]*Z(p)^0, can[1]{[1..3]}, can[2]{[1..3]}]^-1);
        else
            trans := p5id_famMats(p, 6, [[0,0,1]*Z(p)^0, can[1]{[1..3]}, can[2]{[1..3]}]^-1);
        fi;
        can := RREF(base * trans);

        trans := fail;
    fi;
    return trans;
end );



#####################################################################################
## Determines the type of the group corresponding to the provided base of an
## allowed subpace of family 17
## input: a base of the dual of an allowed subspace. Must be in RREF
## output: the corresponding type, either a single integer or a list of two integers
##
BindGlobal( "p5id_fam14id", function(base)
    local p, B, type, k, i, a, b, eig, C, bd, ac, acbd, TD;

    p := Characteristic(base);
    B := base{[1,2]}{[3,4]};

    if Rank(B) = 0 then
        type := 3;

    elif Rank(B) = 1 then

        if B[1][1] <> -B[2][2] then
            type := 4;
        else

            if B[1][2] <> 0*Z(p) then
               i := DLog(Z(p)^2, B[1][2]);
            else
               i := DLog(Z(p)^2, -B[2][1]);
            fi;

            if i <> fail then
               type := 5;
            else
               type := 6;
            fi;
        fi;

    elif Rank(B) = 2 then

        eig := Eigenvalues(GF(p), B);

        if Size(eig) = 0 then
           TD := TraceMat(B)^2/DeterminantMat(B);
           if TD = 0*Z(p) then
             type := 10;
           else
             k := (1+DLog(Z(p), Z(p)^0-4*Z(p)^0/(TD)))/2;
             type := [12, k];
           fi;

        elif Size(eig) = 1 then
            if B = B[1][1]*[[1,0],[0,1]] then
               type := 7;
            else
               if B[1][2] <> 0*Z(p) then
                  i := DLog(Z(p)^2, B[1][2]);
               else
                  i := DLog(Z(p)^2, -B[2][1]);
               fi;

               if i <> fail then
                  type := 8;
               else
                  type := 9;
               fi;
            fi;
        else
            TD := TraceMat(B)^2/DeterminantMat(B);
            k := DLog(Z(p), eig[2]/eig[1]);
            if k > (p-1)/2 then k := -k mod (p-1); fi;
            type := [11, k];
        fi;
    else
        Error("No matching type found in family (14)");
    fi;

    return type;
end );



#####################################################################################
## Calculates the transversal element (a matrix) that maps the provided base to the
## canonical base of the given type from family 17
## input: the type (either an integer or a pair of integers) and the starting base
## output: a matrix
##
BindGlobal( "p5id_fam14trans", function(type, base)
    local p, B, trans, k, i, a, b;

    p := Characteristic(base);
    B := base{[1,2]}{[3,4]};
    trans := IdentityMatrix(GF(p), 4);

    if type = 3 then

    elif type in [5, 6] then
        if B[1][2] = 0*Z(p) then
            trans := trans*p5id_famMats(p, 14, [[0,1],[1,0]]*Z(p)^0);
            B := RREF(base*trans){[1,2]}{[3,4]};
        fi;
        if type = 5 then
            k := 0;
        else
            k := 1;
        fi;

        i := DLog(Z(p)^2, B[1][2]/Z(p)^k);
        b := Z(p)^i;
        i := DLog(Z(p)^2, -B[2][1]/Z(p)^k);
        if i <> fail then
            a := Z(p)^i;
        else
            a := 0*Z(p);
        fi;

        trans := trans*p5id_famMats(p, 14, [[0,-b],[b^-1,a]]*Z(p)^0);

    elif type = 4 then
        trans := fail;
    elif type = 7 then
        trans := p5id_famMats(p, 14, [[B[1][1]^-1, 0], [0,1]]*Z(p)^0);

    elif type in [8, 9] then
        if B[1][2] = 0*Z(p) then
            trans := trans*p5id_famMats(p, 14, [[0,1],[1,0]]*Z(p)^0);
            B := RREF(base*trans){[1,2]}{[3,4]};
        fi;

        if type = 8 then
            k := 0;
        else
            k := 1;
        fi;

        i := DLog(Z(p)^2, B[1][2]/Z(p)^k);
        b := Z(p)^i;
        i := DLog(Z(p)^2, -B[2][1]/Z(p)^k);
        if i <> fail then
            a := Z(p)^i;
        else
            a := 0*Z(p);
        fi;

    elif type = 10 then
        trans := fail;
    elif IsList(type) and type[1] = 11 then
        k := type[2];
        trans := fail;

    elif IsList(type) and type[1] = 12 then
        k := type[2];
        trans :=  fail;

    else
        Error("No such type among groups of family 14.");
    fi;

    return trans;
end );



#####################################################################################
## Determines the type of the group corresponding to the provided dual base of an
## allowed subpace of family 18
## input: a base of the dual of an allowed subspace. Must be in RREF
## output: the corresponding type, either a single integer or a list of two integers
##
BindGlobal( "p5id_fam17id", function(base)
    local p, ps, type, k, i;

    p := Characteristic(base);
    ps := Positions(base[1], 0*Z(p));

    if ps = [1,2,3] then
        type := 28;
    elif ps = [1,3] or ps = [3] then
        type := 29;
    elif ps = [2,3] then
        type := 30;
    elif ps = [1,2] then
        type := 31;
    elif ps = [1] or ps = [] then
        type := 32;
    elif ps = [2] then
        type := 33;
    else
        Error("No matching type found in family (17)");
    fi;

    if type in [29, 32] then
        for k in [1..3] do
            i := DLog(Z(p)^3, (base[1][4]/base[1][2])/Z(p)^k);
            if i <> fail then break; fi;
        od;
        if i = fail then Error("No matching parameter for type"); fi;
        type := [type, k];

    elif type = 33 then
        for k in [1..4] do
            i := DLog(Z(p)^4, base[1][3]/base[1][4]^2*Z(p)^k);
            if i <> fail then break; fi;
        od;
        if i = fail then Error("No matching parameter for type"); fi;
        type := [type, k];
    fi;

    return type;
end );



#####################################################################################
## Calculates the transversal element (a matrix) that maps the provided base to the
## canonical dual base of the given type from family 18
## input: the type (either an integer or a pair of integers) and the starting base
## output: a matrix
##
BindGlobal( "p5id_fam17trans", function(type, base)
    local p, can, trans, k, i, a, b;

    p := Characteristic(base);
    can := [ShallowCopy(base[1])];

    trans := IdentityMatrix(4,base);

    #If first and second entry are non-zero, we can get first = 0 and second = 1
    if base[1][1] = Z(p)^0 and base[1][2] <> 0*Z(p) then
        trans := TransposedMat(p5id_famMats(p, 17,
                                [1, base[1][2]^-1, -base[1][2]^-1]));
    fi;
    #Now every can is either [0,0,...] or [1,0,...] or [0,1,...]

    if type = 28 then
        trans := trans;

    elif type = 31 then
        a := can[1][4];
        trans := trans * TransposedMat(p5id_famMats(p, 17, [1,a,0]));

    elif type = 30 then
        a := can[1][4];
        trans := trans * TransposedMat(p5id_famMats(p, 17, [1,a^-1,0]));

    elif IsList(type) and type[1] = 29 then

        k := type[2];
        i := DLog(Z(p)^3, can[1][4]/Z(p)^k);
        if i = fail then Error("Type 29"); fi;

        a := Z(p)^i;
        trans := trans * TransposedMat(p5id_famMats(p, 17, [a^-1,1,0]));

    elif IsList(type) and type[1] = 32 then

        k := type[2];
        i := DLog(Z(p)^3, can[1][4]/Z(p)^k);
        if i = fail then Error("Type 32"); fi;

        a := Z(p)^i;
        b := can[1][3]/(a*Z(p)^k);
        trans := trans * TransposedMat(p5id_famMats(p, 17, [a^-1,b^-1,0]));

    elif IsList(type) and type[1] = 33 then

        k := type[2];
        i := DLog(Z(p)^4, can[1][3]/can[1][4]^2*Z(p)^k);
        if i = fail then Error("Type 33"); fi;

        a := Z(p)^-i;
        b := can[1][4]/(a^2*Z(p)^k);
        trans := trans * TransposedMat(p5id_famMats(p, 17, [a^-1,b^-1,0]));
    else
        Error("No such type among groups of family 17.");
    fi;
    return trans;
end );



#####################################################################################
## Setup for the orbit calculation and search for canonical represantatives
## input:  group G, prime p, integer fam (16, 17, 18)
## output: record with necessary and useful stuff
##
BindGlobal( "p5id_setupRepsSearch", function(G, p, fam)
    local PCS, nathom, iota, iotaInv, H, C, gensC, phi, gensG, pcgsM, mats,
    rho, U, base, dual;

    PCS := PCentralSeries(G);

    #Set up p-Cover of canonical group isomorphic to G/lam(G)
    nathom := NaturalHomomorphismByNormalSubgroup(G, PCS[Size(PCS)-1]);
    iota := p5id_p4IsoStandard(Image(nathom));
    iotaInv := InverseGeneralMapping(iota.iso);
    H := Image(iota.iso);

    if fam = 6 then
        mats := List(GeneratorsOfGroup(GL(3,p)), g -> p5id_famMats(p, fam, g));
    elif fam = 14 then
        mats := List(GeneratorsOfGroup(GL(2,p)), g -> p5id_famMats(p, fam, g));
    elif fam = 17 then
         mats := List([[1,Z(p),0]*Z(p)^0, [Z(p),Z(p),(p-1)*Z(p)^(2-p)]],
                      v -> p5id_famMats(p, fam, v));
    else
        Error("This should not be reachable\n");
        fam := "rest";
    fi;

    #Set up mapping from p-cover to G via G -nathom-> G/lam(G) <-iota-> H <-phi- C
    C := p5id_getPCover(p, fam);
    gensC := MinimalGeneratingSet(C);
    phi := GroupHomomorphismByImagesNC(C, H, gensC, MinimalGeneratingSet(H));
    pcgsM := Pcgs(Kernel(phi));

    #Determine suitable generators of G by preimages of Image(phi o iota, gensC)
    gensG := List([1..Rank(G)], i ->
                  PreImage(nathom, [Image(iotaInv, Image(phi, gensC[i]))])[1]);

    #Define hom. from p-cover to group and determine kernel and
    rho := GroupHomomorphismByImages(C, G, gensC, gensG);
    U := Kernel(rho);

    #Convert to vectors and dualise if useful
    base := List(Pcgs(U), g -> ExponentsOfPcElement(pcgsM, g)* Z(p)^0);

    if fam in [6, 17] then
        base := NullspaceMat(TransposedMat(base));
        mats := List(mats, x -> TransposedMat(x));
        dual := true;
    else
        dual := false;
    fi;

    base := TriangulizedMat(base);

    return rec(C := C, M := pcgsM, mats := mats, base := base, fam := fam, dual := dual);
end );



#####################################################################################
## Identification function for groups of non-constant families (6, 14, 17)
## input:  group G, prime p, profile ls
## output: pair [p^5, id]
##
BindGlobal( "p5id_iddet", function(G, p, ls, iso)
    local fam, tmp, type, trans, id, aut;

    if ls = [[5,2,0], [5,2,0]] then
        fam := 6;
    elif ls = [[5,3,2,0], [5,3,2,0]] then
        fam := 14;
    elif ls = [[5,3,2,1,0], [5,3,2,1,0]] then
        fam := 17;
    fi;

    tmp := p5id_setupRepsSearch(G, p, fam);
    trans := fail;

    if tmp.fam = 6 then
        type := p5id_fam6id(tmp.base);
        if iso then trans := p5id_fam6trans(type, tmp.base); fi;

    elif tmp.fam = 14 then
        type := p5id_fam14id(tmp.base);
        if iso then trans := p5id_fam14trans(type, tmp.base); fi;

     elif tmp.fam = 17 then
        type := p5id_fam17id(tmp.base);
        if iso then trans := p5id_fam17trans(type, tmp.base); fi;

    else
        Error("Not implemented");
    fi;

    id := IdSmallGroupFromType_p5(p, type);

    if iso and IsBound(trans) then

        aut := GroupHomomorphismByImages(Group(tmp.M), Group(tmp.M), tmp.M,
                                  List([1..Size(tmp.M)],i->PcElementByExponents(tmp.M,trans[i])));
        Error();
    fi;
    return rec(id:=[p^5, id], trans := trans);
end );



#####################################################################################
#####################################################################################
#####################################################################################
#####################################################################################
#####################################################################################



#####################################################################################
## Identification function for groups G of size dividing p^5
## input:  group G
## output: record consiting of group ID and isomorphism SmallGroup (for p^4)
##
BindGlobal( "p5id_Idp5Group", function(GG)
    local ls, param, sz, internal_id, our,type,pos,id,p, isospcgs, res, G,iso,ttt;


    sz := Collected(FactorsInt(Size(GG)));
    if not Size(sz)=1 or not sz[1][2]<=5 then Error("input group must have size p^5"); fi;
    p   := sz[1][1];
    iso := fail;

    isospcgs := false;
    G        := GG;
    if not HasSpecialPcgs(GG) then
        isospcgs := IsomorphismSpecialPcGroup(GG);
        G        := Image(isospcgs);
    fi;


    if sz[1][1] <= 5 then
       #Display("use IdSmallGroup and bf iso");
        ttt := rec(id := IdSmallGroup(G), iso := fail);
        if sz[1][1] in [2,3] or (sz[1][1]=5 and sz[1][2]<5) then ###brute force too slow for 5^5
           if not isospcgs = false then
              ttt.iso := isospcgs*IsomorphismGroups(G,SmallGroup(ttt.id));
            else
               ttt.iso := IsomorphismGroups(G,SmallGroup(ttt.id));
           fi;
        fi;
        SetIdGroup(G,ttt.id);
        SetIdGroup(GG,ttt.id);
        return ttt;
    fi;

    if sz[1][2] <= 4 then
        res := p5id_p4IsoStandard(G);
        SetIdGroup(G,res.id);
        SetIdGroup(GG,res.id);
        if not isospcgs = false then
            res.iso := GroupHomomorphismByImagesNC(GG,Image(res.iso), GeneratorsOfGroup(GG),
                    List(GeneratorsOfGroup(GG),u->Image(res.iso,Image(isospcgs,u))));
            if res.iso = fail then Error("iso fail 1"); fi;
        fi;
        if not Source(res.iso) = GG then Error("dudeldi"); fi;

        return res;

    fi;

    ls    := p5id_profiles(G);

    param := [[[5,2,0],[5,2,0]], [[5,3,2,0],[5,3,2,0]], [[5,3,2,1,0],[5,3,2,1,0]]];

    if not ls in param then
        internal_id := p5id_idp5_constant(G,ls);
        if IsRecord(internal_id) then
            iso := internal_id.iso;
        if not isospcgs = false and not iso = fail then
                iso := GroupHomomorphismByImagesNC(GG,Range(iso), GeneratorsOfGroup(GG),
                    List(GeneratorsOfGroup(GG),u->Image(iso,Image(isospcgs,u))));
                if iso = fail then Error("mhmm"); fi;
            fi;
        internal_id:=internal_id.id;
        else
            internal_id:=internal_id.id;
        fi;

        if p mod 4 = 1 then
            if internal_id = 20 then internal_id := 21;
            elif internal_id = 21 then internal_id := 20; fi;

            if internal_id = 25 then internal_id := 26;
            elif internal_id = 26 then internal_id := 25; fi;
        fi;

        ##translate to GAP id

        our := [1, 2, 8, 14, 27, 28, 41, 42, 43, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40];
        type := [70, 66, 43, 51, 2, 13, 26, 27, 1, 64, 65, 67, 68, 69, 35, 37, 40, 45, 47, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 14, 15, 25, 16, 17, 18, 19, 20, 21, 22, 23, 24];

        pos := Position(our, internal_id);
        if pos = fail then Error("ops"); fi;
        id  := [p^5, IdSmallGroupFromType_p5(p,type[pos])];

    elif ls in param then
            res := p5id_iddet(G, p, ls, false);
            id := res.id;
    fi;

    SetIdGroup(G,id);
    SetIdGroup(GG,id);
    return rec(id := id, iso := iso);
end );
