#############################################################################
##
##  isop4.gi                                                Idp5 package
##
##  Identification of the groups of order dividing p^4, together with an
##  isomorphism onto the corresponding library group (deterministic).
##
#############################################################################

#####################################################################################
## input:  a p-group G of size 1, p, p^2, p^3, or p^4, and optional Boolean argument
## "test"
## output: record with id and iso to SmallGroup(id); if test=true, then do not use NC
## functions
#
BindGlobal( "p5id_p4IsoStandard", function(arg)
    local n, p, e, Gstd, iso, g, h, k, l, U, sz, id, hom, gen, z, i, ord, max, m, new, done, gen_final, im_final, test, G, want, t, O,j, Ug, Upc, pcg, mat, l9, l10, i9, i10, R, kk, ll, hh, gg, hh2;


   if Length(arg)=2 then test := arg[2]; else test:=false; fi;
   G   := arg[1];
   sz  := Size(G);
   n   := Collected(FactorsInt(Size(G)));
   iso := 0;

   if not Length(n)=1 then Error("input needs to be p-group of order dividing p^4"); fi;

   #########################################################

    ## case n=[*,1]
    if Size(n)=1 and n[1][2] = 1 then
        Gstd := SmallGroup(n[1]);
        g := First(Concatenation(GeneratorsOfGroup(G),[One(G)]),x->Order(x)=sz);
        h := First(Concatenation(GeneratorsOfGroup(Gstd),[One(Gstd)]),x->Order(x)=sz);
        gen_final := [g];
        im_final  := [h];
        id        := n[1];

   #########################################################

    ## case n=p^2
    elif Size(n)=1 and n[1][2] = 2 then
        if IsCyclic(G) then
            Gstd := SmallGroup(sz,1);
            g   := First(Concatenation(GeneratorsOfGroup(G),[One(G)]),x->Order(x)=sz);
            h   := First(Concatenation(GeneratorsOfGroup(Gstd),[One(Gstd)]),x->Order(x)=sz);
            gen_final := [g];
            im_final  := [h];
            id  := [sz,1];
        else
            Gstd := SmallGroup(sz,2);
            g   := First(GeneratorsOfGroup(G), x-> not x=One(G));
            U   := Subgroup(G,[g]);
            h   := First(GeneratorsOfGroup(G),x-> not x in U);
            gen_final := [g,h];
            im_final  := [Gstd.1,Gstd.2];
            id  := [sz,2];
        fi;

   ##########################################################

   ## case n=p^3

   elif Size(n)=1 and n[1][2] = 3 then

      p := n[1][1];

      if IsAbelian(G) then

         if IsCyclic(G) then
           Gstd := SmallGroup(sz,1);
           g   := First(GeneratorsOfGroup(G),x->Order(x)=sz);
           h   := First(GeneratorsOfGroup(Gstd),x->Order(x)=sz);
           gen_final := [g];
           im_final  := [h];
           id  := [sz,1];

         elif ForAll(GeneratorsOfGroup(G),x->Order(x) in [1,p]) then
            Gstd := SmallGroup(sz,5);
            h   := First(GeneratorsOfGroup(G),x-> Order(x)=p);
            U   := Subgroup(G,[h]);
            k   := First(GeneratorsOfGroup(G),x-> not x in U);
            U   := Subgroup(G,[h,k]);
            l   := First(GeneratorsOfGroup(G),x-> not x in U);
            gen_final := [h,k,l];
            im_final  := [Gstd.1,Gstd.2,Gstd.3];
            id  := [sz,5];

         else #p^2 x p

            Gstd := SmallGroup(sz,2);
            h   := First(GeneratorsOfGroup(G),x-> Order(x)=p^2);
            U   := Subgroup(G,[h]);
            k   := First(GeneratorsOfGroup(G),x-> not x in U);
            if not Order(k)=p then i := First([1..p-1],x-> Order(h^x*k)=p); k:=h^i*k; fi;
            gen_final := [h,k];
            im_final  := [Gstd.1,Gstd.2];
            id  := [sz,2];

         fi;

      else ## nonabelian

         if sz = 8 then

            id  := IdSmallGroup(G);
            iso := IsomorphismGroups(G,SmallGroup(id));
            return rec(id:=id, iso:=iso);

         else ## odd p

            z   := Centre(G);
            hom := NaturalHomomorphismByNormalSubgroup(G,z);
            gen := List(MinimalGeneratingSet(Image(hom)),x->PreImagesRepresentative(hom,x));

            if Exponent(G)=p then

               Gstd := SmallGroup(sz,3);
               id   := [sz,3];
               gen_final := Concatenation(gen, [Comm( gen[2], gen[1] )] );
               im_final  := [Gstd.1,Gstd.2, Gstd.3];

            else ## exponent p^2 .... this case is still a bit brute force

               Gstd := SmallGroup(sz,4);
               id   := [sz,4];
               ord  := List(gen,Order);
               if not ord[1]=p^2 then gen := gen{[2,1]}; ord := ord{[2,1]}; fi;
               g    := gen[1];
               z    := g^p;
               want := gen[2]^p;
               if ord[1]=p^2 and ord[2]=p^2 then
                  i := First([1..p-1],x-> want=z^x);
                 #i := First([1..p^2-1],x-> Order(gen[1]^x*gen[2])=p);
                  gen[2] := gen[1]^-i*gen[2];
               fi;
               h    := gen[2];
               i    := First([1..p-1],x-> Comm(h^x,g)=z);
               gen_final := [g,h^i,z];
               im_final  := [Gstd.1,Gstd.2, Gstd.3];
            fi;
         fi;
      fi;


   #############################################

   ### p^4
   elif Size(n)=1 and n[1][2] = 4 then
      p := n[1][1];

      ## case p=2 and p=3 bruteforce
      if p in [2,3] then
         id   := IdSmallGroup(G);
         iso  := IsomorphismGroups(G,SmallGroup(id));
         Gstd := SmallGroup(id);
         return rec(id:=id, iso:=iso);


      else ## odd case

         if IsAbelian(G) then
            gen := List(MinimalGeneratingSet(G),x->x);
            ord := List(gen,Order);
            SortParallel(ord,gen);
            ord       := Reversed(ord);
            gen_final := Reversed(gen);
            if ord=[p^4] then
               id     := [sz,1];
               Gstd     := SmallGroup(sz,1);
               im_final :=MinimalGeneratingSet(Gstd);
            elif ord=[p,p,p,p] then
               Gstd     := SmallGroup(sz,15);
               im_final := GeneratorsOfGroup(Gstd);
               id       := [sz,15];
            elif ord = [p^3,p] then
               Gstd     := SmallGroup(sz,5);
               im_final := [Gstd.1,Gstd.2];
               id       := [sz,5];
            elif ord = [p^2,p^2] then
               Gstd := SmallGroup(sz,2);
               im_final := [Gstd.1,Gstd.2];
               id       := [sz,2];
            elif ord = [p^2,p,p] then
               Gstd     := SmallGroup(sz,11);
               im_final := [Gstd.1,Gstd.2,Gstd.3];
               id       := [sz,11];
            fi;


         else ###############################################  nonabelian case

            if Exponent(G) = p^3 then ## C_{p^3} : C_p

               id   := [sz, 6];
               Gstd := SmallGroup(id);
               g    := First(GeneratorsOfGroup(G),x->Order(x)=p^3); ## does exist
               z   := g^(p^2);
               U   := Subgroup(G,[g]);
               repeat h := Random(G); until not h in U;
               if Order(h)=p^3 then
                  want := h^(p^2);
                  i    := First([1..p-1],x-> want = z^x);
                  h    := g^-i * h;
               fi;
               if Order(h)=p^2 then
                  want := h^p;
                  i    := First([1..p-1],x-> want = z^x);
                  h    := g^(-i*p)*h;
               fi;
               i         := First([1..p-1],x-> Comm(h^x,g)=z);
               gen_final := [g,h^i];
               im_final  := [Gstd.1,Gstd.2];


            elif Exponent(G) = p and Size(Centre(G)) = p^2 then # Cp \ltimes C_p^3


               id   := [sz, 12];
               Gstd := SmallGroup(id);
               z    := Centre(G);
               hom := NaturalHomomorphismByNormalSubgroup(G,z);
               gen := List(MinimalGeneratingSet(Image(hom)),x->PreImagesRepresentative(hom,x));
               g   := gen[1];
               h   := gen[2];
               l   := Comm(h,g);
               U   := Subgroup(G,[l]);
               k   := First([z.1,z.2], x-> not x in U);
               gen_final := [g,h,k,l];
               im_final  := [Gstd.1,Gstd.2,Gstd.3,Gstd.4];


            elif Exponent(G)= p and Size(Centre(G)) = p then  # Cp \ltimes C_p^3

               id   := [sz, 7];
               Gstd := SmallGroup(id);
               U    := Centraliser(G,FrattiniSubgroup(G)); #p x p x p
               ## the following is faster than MinimalGeneratingSet(U) for p=101
               Ug   := [];
               for z in GeneratorsOfGroup(U) do
                  if not z in SubgroupNC(G,Ug) then Add(Ug,z); fi;
                  if Size(Ug)=3 then break; fi;
               od;
               l    := MinimalGeneratingSet(Centre(G))[1];
               if not    l in Subgroup(U,Ug{[1,2]}) then t:=[Ug[1],Ug[2],l];
               elif not  l in Subgroup(U,Ug{[2,3]}) then t:=[Ug[2],Ug[3],l];
               elif not  l in Subgroup(U,Ug{[1,3]}) then t:=[Ug[1],Ug[3],l]; fi;
               Upc  := AbelianGroup([p,p,p]);
               g    := First(GeneratorsOfGroup(G),x-> not x in U);
               iso  := GroupHomomorphismByImagesNC(U,Upc,t,MinimalGeneratingSet(Upc));
               pcg  := PcgsByPcSequence(FamilyObj(One(Upc)),List(t,x->Image(iso,x)));
               mat  := List(t,x-> ExponentsOfPcElement(pcg,Image(iso,x^g)))*One(GF(p));
               k    := SolutionMat(mat-mat^0,[0,0,1]*One(GF(p)));
               h    := SolutionMat(mat-mat^0,k);
               k    := PreImagesRepresentative(iso,PcElementByExponents(pcg,List(k,Int)));
               h    := PreImagesRepresentative(iso,PcElementByExponents(pcg,List(h,Int)));
               gen_final := [g,h,k,l];
               im_final  := [Gstd.1,Gstd.2,Gstd.3,Gstd.4];


            elif Exponent(G)=p^2 and Size(Centre(G))=p^2 and IsCyclic(Centre(G)) then
               id := [sz,14];
               Gstd := SmallGroup(id);
               z    := Centre(G);
               hom := NaturalHomomorphismByNormalSubgroup(G,z);
               gen := List(MinimalGeneratingSet(Image(hom)),x->PreImagesRepresentative(hom,x));
               z   := Centre(G);
               g   := gen[1];
               h   := gen[2];
               l   := Comm(h,g);
               z   := First(GeneratorsOfGroup(z),x->Order(x)=p^2);
               i   := First([1..p-1],x-> z^(x*p) = l);
               z   := z^i;
               if Order(g)=p^2 then
                  i   := First([0..p-1],x-> g^p = z^(x*p));
                  g   := g*z^-i;
               fi;
               if Order(h)=p^2 then
                  i   := First([0..p-1],x-> h^p = z^(x*p));
                  h   := h*z^-i;
               fi;
               gen_final := [g,h,z,l];
               im_final  := [Gstd.1,Gstd.2,Gstd.3,Gstd.4];


            elif Exponent(G)=p^2 and RankPGroup(G)=3 then

               id   := [sz,13];
               Gstd := SmallGroup(id);
               z    := Centre(G);
               hom  := NaturalHomomorphismByNormalSubgroup(G,z);
               gen  := List(MinimalGeneratingSet(Image(hom)),x->PreImagesRepresentative(hom,x));
               z   := FrattiniSubgroup(G);
               g   := gen[1];
               h   := gen[2];
               if not Order(g)=p^2 then t := g; g := h; h := t; fi;
               l   := g^p;
               if Order(h)=p^2 then
                  i   := First([0..p-1],x-> h^p = l^(x));
                  h   := h*g^-i;
               fi;
               i   := First([1..p-1],x-> Comm(h^x,g)=l);
               h   := h^i;
               z   := First(GeneratorsOfGroup(Centre(G)),x-> not x in FrattiniSubgroup(G));
               gen_final := [g,h,z,l];
               im_final  := [Gstd.1,Gstd.2,Gstd.3,Gstd.4];

            elif Size(Centre(G))=p^2 and Size(Omega(G,p))=p^3 then
               id   := [sz,3];
               Gstd := SmallGroup(id);
               O    := Omega(G,p);
               g    := First(GeneratorsOfGroup(G),x->Order(x)=p^2);
               l    := g^p;
               U    := Subgroup(O,[l]);
               h    := First(GeneratorsOfGroup(O),x-> not Comm(x,g) in U);
               k    := Comm(h,g);
               gen_final := [g,h,k,l];
               im_final  := [Gstd.1,Gstd.2,Gstd.3,Gstd.4];


            elif Size(Centre(G))=p^2 and Size(Omega(G,p))=p^2 then
               id   := [sz,4];
               Gstd := SmallGroup(id);
               z    := Centre(G);
               hom  := NaturalHomomorphismByNormalSubgroup(G,z);
               gen  := List(MinimalGeneratingSet(Image(hom)),x->PreImagesRepresentative(hom,x));
               g    := gen[1];
               h    := gen[2];
               U    := DerivedSubgroup(G);
               if g^p in U and not h^p in U then
                  t := h; h:=g; g:=t;
               elif not g^p in U and not h^p in U then
                  i    := First([0..p-1],x-> (g^x*h)^p in U);
                  h    := g^i*h;
               fi; #now h^p generates G'
               k    := h^p;
               j    := First([1..p-1],x-> Comm(h,g^x)=k);
               g    := g^j;
               l    := g^p;
               gen_final := [g,h,k,l];
               im_final  := [Gstd.1,Gstd.2,Gstd.3,Gstd.4];


            elif Exponent(Centraliser(G,FrattiniSubgroup(G)))=p then

               id    := [sz,8];
               Gstd := SmallGroup(id);
               U    := Centraliser(G,FrattiniSubgroup(G)); #this is Omega(G,p), but the latter hard to construct!
               ## the following is faster than MinimalGeneratingSet(U) for p=101
               Ug   := [];
               for z in GeneratorsOfGroup(U) do
                  if not z in SubgroupNC(G,Ug) then Add(Ug,z); fi;
                  if Size(Ug)=3 then break; fi;
               od;
               Upc  := AbelianGroup([p,p,p]);
               g    := First(GeneratorsOfGroup(G),x-> not x in U);
               l    := g^p;
               if not    l in Subgroup(U,Ug{[1,2]}) then t:=[Ug[1],Ug[2],l];
               elif not  l in Subgroup(U,Ug{[2,3]}) then t:=[Ug[2],Ug[3],l];
               elif not  l in Subgroup(U,Ug{[1,3]}) then t:=[Ug[1],Ug[3],l]; fi;
               iso  := GroupHomomorphismByImagesNC(U,Upc,t,MinimalGeneratingSet(Upc));
               pcg  := PcgsByPcSequence(FamilyObj(One(Upc)),List(t,x->Image(iso,x)));
               mat  := List(t,x-> ExponentsOfPcElement(pcg,Image(iso,x^g)))*One(GF(p));
               k    := SolutionMat(mat-mat^0,[0,0,1]*One(GF(p)));
               h    := SolutionMat(mat-mat^0,k);
               k    := PreImagesRepresentative(iso,PcElementByExponents(pcg,List(k,Int)));
               h    := PreImagesRepresentative(iso,PcElementByExponents(pcg,List(h,Int)));
               gen_final := [g,h,k,l];
               im_final  := [Gstd.1,Gstd.2,Gstd.3,Gstd.4];


            else   ### last two cases, [p^4,9] and [p^4,10]

               sz   := p^4;
               U    := Centraliser(G,FrattiniSubgroup(G)); #p^2 x p
               h    := First(GeneratorsOfGroup(U),x->Order(x)=p^2);
               g    := Filtered(GeneratorsOfGroup(G),x-> not x in U);
               hh   := First(g,x->Order(x)=p);
               if not hh = fail then
                  g := hh;
               else
                  g    := g[1];
                  l    := h^p;
                  want := g^p;
                  i    := First([0..p-1],x-> l^x=want);
                  g    := g*h^-i;
               fi;

               ## need to find correct power of g that allows us to define
               ## h of order p^2 and then k = h^-1*h^g such that k^g=h^p*k for id 9 and
               ## k^g = h^(Z(p)^-1 * p)*k for id 10

               i   := 0;
               i9  := fail;
               i10 := fail;
               hh  := h^p*h^-1;
               hh2 := h^(Int(Z(p)^-1)*p)*h^-1;
               repeat
                  gg := g^i;
                  if (h^-1*h^(gg))^(gg)= hh*h^(gg) then
                     i9:=i;
                  elif (h^-1*h^(gg))^(gg)= hh2*h^(gg) then
                     i10:=i;
                  fi;
                  i := i+1;
               until i>=p or not i9=fail or not i10=fail;

               if not i9 = fail then
                  id   := [sz,9];
                  Gstd := SmallGroup(id);
                  g         := g^i9;
                  gen_final := [g,h,h^-1*h^g,h^p];
                  im_final  := [Gstd.1,Gstd.2,Gstd.3,Gstd.4];
               elif not i10 = fail then
                   id   := [sz,10];
                   Gstd := SmallGroup(id);
                   g    := g^i10;
                   gen_final := [g,h,h^-1*h^g,h^(Int(Z(p)^-1)*p)];
                   im_final  := [Gstd.1,Gstd.2,Gstd.3,Gstd.4];
               else Error("should not happen"); fi;


            fi;


         fi;

      fi;

   fi;

   if test = true then
      Info(InfoIdp5, 2, "p5id_p4IsoStandard: construct isomorphism with test (no NC)");
      iso := GroupHomomorphismByImages(G,Gstd,gen_final,im_final);
   else
      iso := GroupHomomorphismByImagesNC(G,Gstd,gen_final,im_final);
   fi;

   if iso = fail then Error("oops... something is wrong for ",IdSmallGroup(G)); fi;
   if not iso = 0 then return rec(id := id, iso:=iso); fi;

   Info(InfoIdp5, 1, "p5id_p4IsoStandard: this case is not covered yet");
   return fail;
end );
