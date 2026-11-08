#############################################################################
##
##  isop5.gi                                                Idp5 package
##
##  Isomorphisms from groups of order p^5 onto the library groups: a
##  randomised lifting algorithm.  The main part of this file has been
##  coded with the help of Claude Opus; every isomorphism that is returned
##  is verified.
##
#############################################################################

#####################################################################################
#####################################################################################
#####################################################################################
#####################################################################################
#####################################################################################
#####################################################################################
##
##
## random experimental iso for groups of order p^5
##
##
#####################################################################################
#####################################################################################
#####################################################################################
#####################################################################################



#####################################################################################
#####################################################################################
##
##
## input: group G of order p^5
## output: isom G -> SmallGroup(IdSmallGroup(G))
##
## Randomised algorithm: if this fails, we return fail and one should use ANUPQ
##
## main part of this function has been coded with Claude Opus
## N.B.: returned isomorphism is always correct, but can fail
##
BindGlobal( "p5id_iso_random_bruteforce", function(G)
local id, H, C, i, j, k, gen, ord, genH, ordH, p, CH, nat, natH, Q,QH, isoQ, isoQH, iso, isos,
       im, adj, mychar,itCH,t,newim,r;

  #Print("start iso bf");

   if not HasIdGroup(G) then
      id := p5id_Idp5Group(G);
      if not id.iso=fail then return id.iso; fi;
      id := id.id;
   else
      id := IdSmallGroup(G);
   fi;
   H := SmallGroup(id);


   if IsAbelian(G) then
      gen := List(MinimalGeneratingSet(G),x->x);
      ord := List(gen,Order);
      SortParallel(ord,gen);
      genH :=List(MinimalGeneratingSet(H),x->x);
      ordH := List(genH,Order);
      SortParallel(ordH,genH);
      return GroupHomomorphismByImages(G,H,gen,genH);
   fi;

  ## char is always of rank at most 2; always in Phi and always el-ab!
   p    := PrimePGroup(G);
   mychar := x -> Omega(Intersection([FrattiniSubgroup(x),Centre(x),DerivedSubgroup(x)]),p);
   C    := mychar(G);
   CH   := mychar(H);

   nat  := NaturalHomomorphismByNormalSubgroup(G,C);
   natH := NaturalHomomorphismByNormalSubgroup(H,CH);
   Q    := Image(nat);
   QH   := Image(natH);

  ##Print("CONTINUE BF HERE",IdSmallGroup(G));

################################################################################# START OF CLAUDE CODE!!!!!

######## the following has been coded with the help of Claude.ai;
######## we verify the output, so the returned value will never be incorrect
   ##
   ## Isomorphism G --> H for the standard copy H = SmallGroup(p^5,i) of G.
   ##
   ## All cases rest on one lifting step. Let x_1,...,x_n be a pcgs of G, let K be an
   ## elementary abelian subgroup of Z(H) cap Phi(H), and let im[k] in H realise a given
   ## isomorphism G/K' --> H/K. A homomorphism G --> H inducing it must map
   ##      x_k --> im[k]*c_k     with   c_k in K,
   ## and the power-commutator relations of G turn this into a linear system A*X = B
   ## over GF(p), the rows of A being the exponent vectors of the relations and the rows
   ## of X the coordinates of the c_k. Here A does not depend on the isomorphism and is
   ## set up once; every solution yields an isomorphism, and unsolvability means that the
   ## given isomorphism does not lift. Variants allow a normal non-central kernel
   ## (r.liftmod), an abelian kernel of exponent p^2 (r.liftab) and a central cyclic
   ## kernel of order p^2 (r.liftcyc). Everything returned is verified.
   ##
   ## The cases are tried in this order.
   ##
    ##  (A)   Phi(G) elementary abelian and central: G is determined by the commutator
   ##        and p-power maps on V = G/Phi(G), so a compatible isomorphism V --> V' is
   ##        constructed by linear algebra and lifted.
   ##  (A2)-(A5)  rank 3 (A2,A3) and rank 2 (A4,A5): the commutator and p-power maps
   ##        between the layers of G are preserved by an isomorphism up to scalars,
   ##        which leaves O(p) candidates for the map induced on V; each candidate is
   ##        lifted, or discarded, by linear algebra.
   ##  (B)   the admissible characteristic subgroups K, smallest first (the larger the
   ##        quotient, the more it determines): the k-th subgroup of G and the k-th of H
   ##        come from the same recipe, hence correspond under every isomorphism, and
   ##        the isomorphism G/K --> H/K from the standard copies is lifted.
   ##  (B2)  the subgroups of order p of C are NOT characteristic, so there is no
   ##        canonical partner in H: we fix one such subgroup in G and try ALL p+1
   ##        candidates in H, which is complete because an isomorphism maps C onto CH.
   ##  (C)   bounded random search: modify the isomorphism of a quotient by random
   ##        automorphisms of that quotient until it lifts.
   ##

   r      := rec( pcgG := Pcgs(G), rel := [], exp := [] );
   r.n    := Length(r.pcgG);
   r.one  := One(GF(p));
   r.oneH := One(H);

   ## the relations of the pc presentation of G wrt r.pcgG: the pair [i,0] stands for
   ## the relation with left hand side x_i^p and [i,j] for the one with left hand side
   ## Comm(x_j,x_i); r.exp holds the exponent vectors of the right hand sides
   for i in [1..r.n] do
      Add(r.rel, [i,0]);
      Add(r.exp, ExponentsOfPcElement(r.pcgG, r.pcgG[i]^p));
      for j in [i+1..r.n] do
         Add(r.rel, [i,j]);
         Add(r.exp, ExponentsOfPcElement(r.pcgG, Comm(r.pcgG[j], r.pcgG[i])));
      od;
   od;
   r.mat := TransposedMat(r.one * r.exp);
   ## the exponent vectors are sparse: only these positions contribute to the products
   ## in r.liftu below, which is the innermost loop of the whole function
   r.sup  := List(r.exp, v -> Filtered([1..r.n], l -> not v[l] = 0));
   r.nrel := Length(r.rel);

   ## A*X = B is solvable if and only if v*B = 0 for every v in the left null space of
   ## A; as A does not depend on the isomorphism, that null space is computed once. The
   ## conditions are checked in r.liftu while B is built, so a hopeless candidate is
   ## discarded after a few relations, which is what makes the search in (C) cheap.
   r.left := NullspaceMat(r.one * r.exp);
   r.test := List([1..r.nrel], k -> []);
   for t in r.left do
      k := Maximum(Filtered([1..r.nrel], j -> not IsZero(t[j])));
      Add(r.test[k], rec(sup := Filtered([1..k], j -> not IsZero(t[j])), v := t));
   od;

   ## r.liftu(u,n2,K): solves the system, where u is the list of images in H/K of the
   ## pcgs of G under the isomorphism to be lifted; returns the lift G --> H, or fail.
   ## Using images rather than the map itself keeps one try in (C) cheap.
   r.liftu := function(u, n2, K)
      local pcgK, d, im, rhs, k, l, v, w, sol, c, cond, hom;
      pcgK := Pcgs(K);
      d    := Length(pcgK);
      im   := List(u, y -> PreImagesRepresentative(n2, y));
      rhs  := [];
      for k in [1..r.nrel] do
         if r.rel[k][2] = 0 then
            w := im[r.rel[k][1]]^p;
         else
            w := Comm(im[r.rel[k][2]], im[r.rel[k][1]]);
         fi;
         v := r.oneH;
         for l in r.sup[k] do v := v * im[l]^r.exp[k][l]; od;
         w := LeftQuotient(v, w);
         if not w in K then return fail; fi;
         Add(rhs, r.one * ExponentsOfPcElement(pcgK, w));
         ## discard this candidate as soon as one solvability condition fails
         for cond in r.test[k] do
            if not IsZero(Sum(cond.sup, l -> cond.v[l]*rhs[l])) then return fail; fi;
         od;
      od;

      ## solve A*X = B column by column; the k-th row of X gives the element c_k
      ## the conditions above guarantee that the system is solvable
      sol := List(TransposedMat(rhs), v -> SolutionMat(r.mat, v));
      if ForAny(sol, v -> v = fail) then return fail; fi;
      c   := List([1..r.n], k -> PcElementByExponents(pcgK,
                    List([1..d], l -> IntFFE(sol[l][k]))));
      hom := GroupHomomorphismByImages(G, H, AsList(r.pcgG),
                    List([1..r.n], k -> im[k]*c[k]));
      if hom = fail or not IsBijective(hom) then return fail; fi;
      return hom;
   end;

   ## r.lift(map,n1,n2,K): the same for an isomorphism map: G/K' --> H/K, where
   ## n1: G --> G/K' and n2: H --> H/K are the natural homomorphisms
   r.lift := function(map, n1, n2, K)
      return r.liftu(List(r.pcgG, x -> Image(map, Image(n1, x))), n2, K);
   end;

   ## r.powtab/r.powcol: the powers of the images that the relations need, computed once
   ## and reused; for a perturbed list of images only one column has to be redone.
   ## r.relvals(im,pw,K,pcgK,wf): the values of the relations of G at im, read in K;
   ## fail if one of them is not in K. If wf is the coordinate vector in K/L for some L
   ## containing [K,H] and K^p, then the wf-part of the equations again has the matrix
   ## r.exp, so the precomputed conditions r.test discard a hopeless im early.
   r.eneed := List([1..r.n], l -> Set(Concatenation(
                 Filtered(List([1..r.nrel], k -> r.exp[k][l]), e -> e > 1), [p])));

   r.powcol := function(x, l)
      local t, e;
      t := [];   t[1] := x;
      for e in r.eneed[l] do t[e] := x^e; od;
      return t;
   end;

   r.powtab := function(im)
      return List([1..r.n], l -> r.powcol(im[l], l));
   end;

   r.relvals := function(im, pw, K, pcgK, wf)
      local out, wv, k, l, v, w, cond;
      out := [];   wv := [];
      for k in [1..r.nrel] do
         if r.rel[k][2] = 0 then
            w := pw[r.rel[k][1]][p];
         else
            w := Comm(im[r.rel[k][2]], im[r.rel[k][1]]);
         fi;
         v := r.oneH;
         for l in r.sup[k] do v := v * pw[l][r.exp[k][l]]; od;
         w := LeftQuotient(v, w);
         if not w in K then return fail; fi;
         if not wf = fail then
            Add(wv, wf(w));
            for cond in r.test[k] do
               if not IsZero(Sum(cond.sup, l -> cond.v[l]*wv[l])) then return fail; fi;
            od;
         fi;
         Add(out, r.one * ExponentsOfPcElement(pcgK, w));
      od;
      return out;
   end;

   ## r.liftmod(map,n1,n2,K,wf): as r.lift, but K only has to be elementary abelian and
   ## NORMAL in H. The conditions on the c_k stay linear over GF(p); their coefficients
   ## involve the action of H on K and are read off by perturbing one image at a time.
   r.liftmod := function(map, n1, n2, K, wf)
      return r.liftmodu(List(r.pcgG,
                x -> PreImagesRepresentative(n2, Image(map, Image(n1, x)))), K, wf);
   end;

   ## r.liftmodu(im,K,wf): as r.liftmod, but for images that are already given in H
   r.liftmodu := function(im, K, wf)
      local pcgK, d, v0, cols, l, t, k, im2, pw, pw2, v, sol, c, hom;
      pcgK := Pcgs(K);
      d    := Length(pcgK);
      pw   := r.powtab(im);
      v0   := r.relvals(im, pw, K, pcgK, wf);
      if v0 = fail then return fail; fi;
      cols := [];
      for l in [1..r.n] do
         for t in [1..d] do
            im2      := ShallowCopy(im);
            im2[l]   := im[l]*pcgK[t];
            pw2      := ShallowCopy(pw);
            pw2[l]   := r.powcol(im2[l], l);
            v        := r.relvals(im2, pw2, K, pcgK, fail);
            if v = fail then return fail; fi;
            Add(cols, Concatenation(List([1..r.nrel], k -> v[k]-v0[k])));
         od;
      od;
      sol := SolutionMat(cols, Concatenation(List(v0, x -> -x)));
      if sol = fail then return fail; fi;
      c   := List([1..r.n], l -> PcElementByExponents(pcgK,
                   List([1..d], t -> IntFFE(sol[(l-1)*d+t]))));
      hom := GroupHomomorphismByImages(G, H, AsList(r.pcgG),
                   List([1..r.n], l -> im[l]*c[l]));
      if hom = fail or not IsBijective(hom) then return fail; fi;
      return hom;
   end;

   ## r.mkwf(K): the coordinate vector in K/(K^p*[K,H]), the largest quotient of K on
   ## which the lifting equations have the image independent matrix r.exp
   r.mkwf := function(K)
      local L, nL, f;
      L  := ClosureGroup(Agemo(K, p), CommutatorSubgroup(K, H));
      if Size(L) = Size(K) then return fail; fi;
      nL := NaturalHomomorphismByNormalSubgroup(K, L);
      f  := Pcgs(Image(nL));
      return w -> r.one*ExponentsOfPcElement(f, Image(nL, w));
   end;

   ## r.relvalsab(im,pw,K,gens,wf): as r.relvals, but read in the abelian group K with
   ## respect to independent generators, so that K may have exponent p^2
   r.relvalsab := function(im, pw, K, gens, wf)
      local out, wv, k, l, v, w, cond;
      out := [];   wv := [];
      for k in [1..r.nrel] do
         if r.rel[k][2] = 0 then
            w := pw[r.rel[k][1]][p];
         else
            w := Comm(im[r.rel[k][2]], im[r.rel[k][1]]);
         fi;
         v := r.oneH;
         for l in r.sup[k] do v := v * pw[l][r.exp[k][l]]; od;
         w := LeftQuotient(v, w);
         if not w in K then return fail; fi;
         if not wf = fail then
            Add(wv, wf(w));
            for cond in r.test[k] do
               if not IsZero(Sum(cond.sup, l -> cond.v[l]*wv[l])) then return fail; fi;
            od;
         fi;
         Add(out, IndependentGeneratorExponents(K, w));
      od;
      return out;
   end;

   ## r.liftab(im,K,wf): lift through a normal ABELIAN kernel K, possibly of exponent
   ## p^2 (for an elementary abelian K, r.liftmodu is faster). The c_l enter through a
   ## homomorphism K^n --> K^nrel, again read off by perturbation; the system is solved
   ## over the integers, with the orders of the generators added as relations.
   r.liftab := function(im, K, wf)
      local gens, ords, rk, pw, v0, cols, l, t, im2, pw2, v, rows, targ, k, j, e, sol,
            c, hom;
      gens := IndependentGeneratorsOfAbelianGroup(K);
      ords := List(gens, Order);
      rk   := Length(gens);
      pw   := r.powtab(im);
      v0   := r.relvalsab(im, pw, K, gens, wf);
      if v0 = fail then return fail; fi;
      cols := [];
      for l in [1..r.n] do
         for t in [1..rk] do
            im2    := ShallowCopy(im);   im2[l] := im[l]*gens[t];
            pw2    := ShallowCopy(pw);   pw2[l] := r.powcol(im2[l], l);
            v      := r.relvalsab(im2, pw2, K, gens, fail);
            if v = fail then return fail; fi;
            Add(cols, Concatenation(List([1..r.nrel], k -> v[k]-v0[k])));
         od;
      od;
      rows := ShallowCopy(cols);
      for k in [1..r.nrel] do
         for j in [1..rk] do
            e := List([1..r.nrel*rk], i -> 0);
            e[(k-1)*rk+j] := ords[j];
            Add(rows, e);
         od;
      od;
      targ := Concatenation(List(v0, x -> -x));
      ## the reduction modulo p of the system is a cheap necessary condition, and the
      ## integer solver below is comparatively expensive
      if SolutionMat(r.one*cols, r.one*targ) = fail then return fail; fi;
      sol := SolutionIntMat(rows, targ);
      if sol = fail then return fail; fi;
      c    := List([1..r.n],
                 l -> Product([1..rk], t -> gens[t]^sol[(l-1)*rk+t]));
      hom  := GroupHomomorphismByImages(G, H, AsList(r.pcgG),
                    List([1..r.n], l -> im[l]*c[l]));
      if hom = fail or not IsBijective(hom) then return fail; fi;
      return hom;
   end;

   ## r.std(gK,KH): the isomorphism G/K --> H/KH from the standard copies of the two
   ## quotients (of order dividing p^4), together with the natural homomorphisms; fail
   ## if the quotients are not isomorphic. r.stdG(K) prepares the source side, which in
   ## (B2) is the same for all p+1 candidates KH.
   r.stdG := function(K)
      local n1;
      n1 := NaturalHomomorphismByNormalSubgroup(G, K);
      return rec(nat := n1, a := p5id_Idp5Group(Image(n1)));
   end;

   r.std := function(gK, KH)
      local n2, b, s;
      if gK.a.iso = fail then return fail; fi;
      n2 := NaturalHomomorphismByNormalSubgroup(H, KH);
      b  := p5id_Idp5Group(Image(n2));
      if b.iso = fail or not gK.a.id = b.id then return fail; fi;
      s  := GroupHomomorphismByImagesNC(Range(gK.a.iso), Range(b.iso),
                Pcgs(Range(gK.a.iso)), Pcgs(Range(b.iso)));
      return rec(map := gK.a.iso*s*InverseGeneralMapping(b.iso), nat := gK.nat,
                 natH := n2, K := KH, Q := Image(n2));
   end;

   ##
   ## (2) the class 2 case: G/C elementary abelian
   ##
   ## r.form(n,K): structure constants wrt Pcgs(Image(n)) and Pcgs(K), that is, B[k] is
   ## the matrix of the k-th coordinate of the commutator map and P[i] the coordinates
   ## of the p-th power of the i-th generator
   r.form := function(n, K)
      local q, f, pz, m, d, li;
      q  := Image(n);   f := Pcgs(q);   pz := Pcgs(K);
      m  := Length(f);  d := Length(pz);
      li := u -> PreImagesRepresentative(n, u);
      return rec( m := m, d := d,
        B := List([1..d], k -> List([1..m], i -> List([1..m], j ->
               r.one*ExponentsOfPcElement(pz, Comm(li(f[i]), li(f[j])))[k]))),
        P := List([1..m], i -> r.one*ExponentsOfPcElement(pz, li(f[i])^p)) );
   end;

   ## r.constr1(dG,dH): dim C = 1, so C --> CH is multiplication by a scalar lam. For
   ## each lam the images of a basis of V are determined one at a time, the conditions
   ## on the next image being linear. The basis is adapted to rad(b) = Z(G)/C, and if b
   ## is nondegenerate and pi nonzero, the image of the first basis vector is fixed.
   r.constr1 := function(dG, dH, tries)
      local RG, RH, xs, fix, s, lam, att, ys, i, j, k, M, tv, sol, ns, y, v, ok;
      RG := NullspaceMat(dG.B[1]);   RH := NullspaceMat(dH.B[1]);
      if not Length(RG) = Length(RH) then return fail; fi;
      s   := Length(RG);
      xs  := ShallowCopy(RG);
      fix := [];
      if s = 0 then
         v := SolutionMat(dG.B[1], List(dG.P, u -> u[1]));
         y := SolutionMat(dH.B[1], List(dH.P, u -> u[1]));
         if not (v = fail or y = fail or IsZero(v) or IsZero(y)) then
            xs := [v];   fix := [y];
         fi;
      fi;
      for v in IdentityMat(dG.m, GF(p)) do
         if RankMat(Concatenation(xs,[v])) > Length(xs) then Add(xs,v); fi;
      od;
      for lam in Filtered(AsList(GF(p)), x -> not IsZero(x)) do
        for att in [1..tries] do
          ys := ShallowCopy(fix);   ok := true;
          for i in [Length(fix)+1..dG.m] do
             M  := [ List(dH.P, v -> v[1]) ];
             tv := [ lam*(xs[i]*List(dG.P, v -> v[1])) ];
             for j in [1..i-1] do
                Add(M, ys[j]*dH.B[1]);
                Add(tv, lam*(xs[j]*dG.B[1]*xs[i]));
             od;
             if i <= s then                      ## x_i is in the radical of b
                for k in [1..dH.m] do
                   Add(M, List([1..dH.m], l -> dH.B[1][l][k]));
                   Add(tv, Zero(GF(p)));
                od;
             fi;
             sol := SolutionMat(TransposedMat(M), tv);
             if sol = fail then ok := false; break; fi;
             ns := NullspaceMat(TransposedMat(M));
             y  := fail;
             for k in [1..30] do
                v := sol;
                for j in [1..Length(ns)] do v := v + Random(GF(p))*ns[j]; od;
                if RankMat(Concatenation(ys,[v])) > Length(ys) and
                   (i <= s or not IsZero(v*dH.B[1])) then
                   y := v;  break;
                fi;
                if ns = [] then break; fi;
             od;
             if y = fail then ok := false; break; fi;
             Add(ys,y);
          od;
          if ok and RankMat(ys) = dG.m then return rec(x := xs, y := ys); fi;
        od;
      od;
      return fail;
   end;

   ## r.plane(dat): here dim V = 3 and dim C = 2, so ker(b) = <om> is 1-dimensional and
   ## om is decomposable; the plane it spans is characteristic (its preimage is the
   ## unique abelian maximal subgroup). Returns the form with that kernel and a basis.
   r.plane := function(dat)
      local ns, om, phi;
      ns := NullspaceMat([ List(dat.B, M -> M[1][2]), List(dat.B, M -> M[1][3]),
                           List(dat.B, M -> M[2][3]) ]);
      if not Length(ns) = 1 then return fail; fi;
      om  := ns[1];
      phi := [ om[3], -om[2], om[1] ];
      return rec(phi := phi, bas := NullspaceMat(TransposedMat([phi])));
   end;

   ## r.constr2(dG,dH): dim V = 3 and dim C = 2. With a basis x1,x2 of the plane and x3
   ## outside it, the map theta on C is determined by the images y1,y2 and the scalar mu
   ## of x3, and the p-power conditions are then linear in y1,y2 and w; so only the p-1
   ## values of mu have to be tried.
   r.constr2 := function(dG, dH)
      local pG, pH, x1, x2, x3, z1, z2, z, cG1, cG2, ab, bz1, bz2, pz1, pz2, pzz,
            i, k, mu, M, tv, e, sol, ns, att, v, y1, y2, w;
      pG := r.plane(dG);   pH := r.plane(dH);
      if pG = fail or pH = fail then return fail; fi;
      x1 := pG.bas[1];  x2 := pG.bas[2];
      x3 := First(IdentityMat(3,GF(p)), v -> not IsZero(pG.phi*v));
      z1 := pH.bas[1];  z2 := pH.bas[2];
      z  := First(IdentityMat(3,GF(p)), v -> not IsZero(pH.phi*v));
      cG1 := List(dG.B, M -> x1*M*x3);
      cG2 := List(dG.B, M -> x2*M*x3);
      if not RankMat([cG1,cG2]) = 2 then return fail; fi;
      ## pi(x_i) = ab[i][1]*cG1 + ab[i][2]*cG2
      ab := List([x1,x2,x3], v -> SolutionMat([cG1,cG2],
                 Sum([1..3], i -> v[i]*dG.P[i])));
      if ForAny(ab, v -> v = fail) then return fail; fi;
      bz1 := List(dH.B, M -> z1*M*z);      ## b'(z1,z)
      bz2 := List(dH.B, M -> z2*M*z);      ## b'(z2,z)
      pz1 := dH.P[1]*z1[1] + dH.P[2]*z1[2] + dH.P[3]*z1[3];   ## pi'(z1)
      pz2 := dH.P[1]*z2[1] + dH.P[2]*z2[2] + dH.P[3]*z2[3];   ## pi'(z2)
      pzz := dH.P[1]*z[1]  + dH.P[2]*z[2]  + dH.P[3]*z[3];    ## pi'(z)
      for mu in Filtered(AsList(GF(p)), x -> not IsZero(x)) do
         ## unknowns: y1 = e1*z1+e2*z2, y2 = e3*z1+e4*z2, w = e5*z1+e6*z2
         M := [];  tv := [];
         for i in [1..3] do
            for k in [1,2] do
               e := [ -mu*ab[i][1]*bz1[k], -mu*ab[i][1]*bz2[k],
                      -mu*ab[i][2]*bz1[k], -mu*ab[i][2]*bz2[k],
                      Zero(GF(p)), Zero(GF(p)) ];
               if i = 1 then
                  e[1] := e[1] + pz1[k];   e[2] := e[2] + pz2[k];
                  Add(tv, Zero(GF(p)));
               elif i = 2 then
                  e[3] := e[3] + pz1[k];   e[4] := e[4] + pz2[k];
                  Add(tv, Zero(GF(p)));
               else
                  e[5] := pz1[k];          e[6] := pz2[k];
                  Add(tv, -mu*pzz[k]);
               fi;
               Add(M, e);
            od;
         od;
         sol := SolutionMat(TransposedMat(M), tv);
         if sol = fail then continue; fi;
         ns := NullspaceMat(TransposedMat(M));
         for att in [1..20] do
            e := sol;
            for v in ns do e := e + Random(GF(p))*v; od;
            y1 := e[1]*z1 + e[2]*z2;
            y2 := e[3]*z1 + e[4]*z2;
            w  := e[5]*z1 + e[6]*z2;
            if RankMat([y1,y2]) = 2 then
               return rec(x := [x1,x2,x3], y := [y1,y2,mu*z+w]);
            fi;
            if ns = [] then break; fi;
         od;
      od;
      return fail;
   end;

   ## r.chars(x): the characteristic subgroups of x that can play the role of C, that is,
   ## the elementary abelian ones inside Z(x) cap Phi(x). A fixed recipe, so entry k for
   ## G and entry k for H correspond to each other.
   r.chars := function(x)
      local b, l, s, u;
      l := LowerCentralSeries(x);
      b := [ FrattiniSubgroup(x), Centre(x), DerivedSubgroup(x), Agemo(x,p),
             l[Length(l)-1], Agemo(Centre(x),p) ];
      return List(Filtered(Combinations([1..Length(b)]), s -> not s = []),
                  function(s)
                     u := Intersection(Concatenation([b[1],b[2]], b{s}));
                     if Size(u) = 1 then return u; fi;
                     return Omega(u,p);
                  end);
   end;


   ## ---------------------------------------------------------------------------
   ## (A) construction: G of class 2 with Phi(G) elementary abelian and central
   ## ---------------------------------------------------------------------------
   r.K := FrattiniSubgroup(G);
   if IsElementaryAbelian(r.K) and IsSubset(Centre(G), r.K) then
      r.KH   := FrattiniSubgroup(H);
      r.natK := NaturalHomomorphismByNormalSubgroup(G, r.K);
      r.natH := NaturalHomomorphismByNormalSubgroup(H, r.KH);
      r.V    := Image(r.natK);
      r.VH   := Image(r.natH);
      r.fG   := r.form(r.natK, r.K);
      r.fH   := r.form(r.natH, r.KH);
      t      := fail;
      if r.fH.d = 1 then
         t := r.constr1(r.fG, r.fH, 10);
      elif r.fH.d = 2 and r.fH.m = 3 then
         t := r.constr2(r.fG, r.fH);
      elif r.fH.m*(r.fH.m-1)/2 + r.fH.m = r.fH.d then
          ## the commutator values and the p-th powers of a basis of V span Phi(G), so
          ## there is no condition: every isomorphism V --> V' is compatible with (b,pi)
         t := rec(x := IdentityMat(r.fG.m, GF(p)), y := IdentityMat(r.fH.m, GF(p)));
      fi;
      if not t = fail then
         r.alp := GroupHomomorphismByImagesNC(r.V, r.VH,
                     List(t.x, v -> PcElementByExponents(Pcgs(r.V),  List(v, IntFFE))),
                     List(t.y, v -> PcElementByExponents(Pcgs(r.VH), List(v, IntFFE))));
         if not r.alp = fail then
            newim := r.lift(r.alp, r.natK, r.natH, r.KH);
            if not newim = fail then
               Info(InfoIdp5, 2, "p5id_iso_random_bruteforce: case A for ",id);
               return newim;
            fi;
         fi;
      fi;
   fi;

   ## ---------------------------------------------------------------------------
   ## (A2) class 3, Phi(G) elementary abelian of order p^2, gamma_3 of order p, rank 3.
   ## With V = G/Phi(G), W = Phi(G)/gamma_3 and C = gamma_3 the commutator maps
   ## V x V --> W and V x W --> C are onto, so an isomorphism is determined by the map
   ## alpha induced on V together with the scalars mu on W and nu on C; alpha must also
   ## match the p-power map and map rad(b) to rad(b'). In the unknowns (alpha,lambda,s,c)
   ## with lambda = nu/mu these conditions are HOMOGENEOUS linear -- rescaling alpha is
   ## not a symmetry, so the scalars must not be normalised away -- and it is enough to
   ## run through the projective points of the solution space, the scalar factor of alpha
   ## being recovered from alpha b' alpha^T = mu*b. Each candidate is lifted (r.liftmod).
   ## ---------------------------------------------------------------------------
   ##
   r.graded := function(X)
      local Ph, g3, nV, V, f, li, nW, W, w0, c0, cw, cc, dat, i, j;
      Ph := FrattiniSubgroup(X);
      g3 := LowerCentralSeries(X)[3];
      nV := NaturalHomomorphismByNormalSubgroup(X, Ph);
      V  := Image(nV);   f := Pcgs(V);
      li := u -> PreImagesRepresentative(nV, u);
      nW := NaturalHomomorphismByNormalSubgroup(Ph, g3);
      W  := Image(nW);
      w0 := PreImagesRepresentative(nW, Pcgs(W)[1]);
      c0 := Pcgs(g3)[1];
      cw := u -> r.one*ExponentsOfPcElement(Pcgs(W), Image(nW,u))[1];
      cc := u -> r.one*ExponentsOfPcElement(Pcgs(g3), u)[1];
      dat := rec(Ph := Ph, g3 := g3, nat := nV, V := V, f := f, w0 := w0, c0 := c0,
                 nW := nW, W := W, m := Length(f));
      dat.b   := List([1..dat.m], i -> List([1..dat.m],
                        j -> cw(Comm(li(f[i]), li(f[j])))));
      dat.phi := List([1..dat.m], i -> cc(Comm(w0, li(f[i]))));
      dat.pi1 := List([1..dat.m], i -> cw(li(f[i])^p));
      if IsZero(dat.pi1) then
         dat.pi2 := List([1..dat.m], i -> cc(li(f[i])^p));
      else
         dat.pi2 := fail;
      fi;
      return dat;
   end;

   ## r.cands(dG,dH): the candidates for alpha, as 3x3 matrices over GF(p); see above
   r.cands := function(dG, dH, lim)
      local res, rG, rH, M, row, k, c, l, ns, d, npts, pts, i, e, v, A,
            s1, s2, w, mu, t, pos, zeropi;
      rG := NullspaceMat(dG.b);   rH := NullspaceMat(dH.b);
      if not (Length(rG) = 1 and Length(rH) = 1) then return []; fi;
      rG := rG[1];   rH := rH[1];
      if not (dG.pi2 = fail) = (dH.pi2 = fail) then return []; fi;
      zeropi := not dG.pi2 = fail and IsZero(dG.pi2);
      if not zeropi = (not dH.pi2 = fail and IsZero(dH.pi2)) then return []; fi;
      ## unknowns: alpha (positions 1..9), lambda (10), s (11), c (12)
      M := [];
      for k in [1..3] do                         ## alpha_k*phi' = lambda*phi_k
         row := List([1..12], c -> Zero(GF(p)));
         for c in [1..3] do row[3*(k-1)+c] := dH.phi[c]; od;
         row[10] := -dG.phi[k];
         Add(M, row);
      od;
      for k in [1..3] do                         ## the p-power condition
         row := List([1..12], c -> Zero(GF(p)));
         if dG.pi2 = fail then
            for c in [1..3] do row[3*(k-1)+c] := dH.pi1[c]; od;
            row[11] := -dG.pi1[k];
         else
            for c in [1..3] do row[3*(k-1)+c] := dH.pi2[c]; od;
            row[11] := -dG.pi2[k];
         fi;
         Add(M, row);
      od;
      if zeropi then                             ## then s is not determined at all
         row := List([1..12], c -> Zero(GF(p)));   row[11] := One(GF(p));   Add(M, row);
      fi;
      for k in [1..3] do                         ## alpha(rad b) = c*rad b'
         row := List([1..12], c -> Zero(GF(p)));
         for l in [1..3] do row[3*(l-1)+k] := rG[l]; od;
         row[12] := -rH[k];
         Add(M, row);
      od;
      ns := NullspaceMat(TransposedMat(M));
      d  := Length(ns);
      if d = 0 then return []; fi;
      ## the projective points of the solution space, or a sample if there are too many
      npts := (p^d-1)/(p-1);   pts := [];   r.full := npts <= lim;
      if r.full then
         for i in [1..d] do
            for e in Tuples(AsList(GF(p)), d-i) do
               v := ShallowCopy(ns[i]);
               for k in [1..d-i] do v := v + e[k]*ns[i+k]; od;
               Add(pts, v);
            od;
         od;
      else
         pts := List([1..lim], i -> Sum(ns, u -> Random(GF(p))*u));
      fi;
      pos := First(Cartesian([1..3],[1..3]), q -> not IsZero(dG.b[q[1]][q[2]]));
      res := [];
      for v in pts do
         A := [v{[1..3]}, v{[4..6]}, v{[7..9]}];
         if IsZero(DeterminantMat(A)) then continue; fi;
         s1 := v[10];   s2 := v[11];
         if IsZero(s1) then continue; fi;
         ## alpha must turn b' into a multiple of b; this also determines mu
         w  := A*dH.b*TransposedMat(A);
         mu := w[pos[1]][pos[2]]/dG.b[pos[1]][pos[2]];
         if IsZero(mu) or not w = mu*dG.b then continue; fi;
         if zeropi then                          ## every scalar multiple works
            Add(res, A);
         elif dG.pi2 = fail then                 ## s = mu fixes the factor
            if IsZero(s2) then continue; fi;
            Add(res, (s2/mu)*A);
         else                                    ## s = nu = lambda*mu fixes it up to a sign
            if IsZero(s2) then continue; fi;
            t := RootFFE(GF(p), s2/(s1*mu), 2);
            if t = fail then continue; fi;
            Add(res, t*A);   Add(res, -t*A);
         fi;
      od;
      Info(InfoIdp5, 3, "p5id_iso_random_bruteforce: (A2) nullity ", d, ", ",
           Length(res), " candidates");
      ## the points are produced in a systematic order, so scan them in random order
      return Permuted(res, Random(SymmetricGroup(Length(res))));
   end;

   if Size(FrattiniSubgroup(G)) = p^2 and IsElementaryAbelian(FrattiniSubgroup(G))
      and NilpotencyClassOfGroup(G) = 3
      and Size(LowerCentralSeries(G)[3]) = p then
      r.dG := r.graded(G);
      r.dH := r.graded(H);
      if r.dG.m = 3 and not IsZero(r.dG.phi) then
         ## the component of Phi(H) modulo [Phi(H),H]; see r.relvals
         r.wf := r.mkwf(r.dH.Ph);
         ## a small sample of candidates first, a large one only if that fails
         r.tryA2 := function(lim)
            local t, alp, new;
            for t in r.cands(r.dG, r.dH, lim) do
               alp := GroupHomomorphismByImagesNC(r.dG.V, r.dH.V, AsList(r.dG.f),
                         List(t, v -> PcElementByExponents(r.dH.f, List(v, IntFFE))));
               if alp = fail then continue; fi;
               new := r.liftmod(alp, r.dG.nat, r.dH.nat, r.dH.Ph, r.wf);
               if not new = fail then return new; fi;
            od;
            return fail;
         end;
         newim := r.tryA2(2000);
         if newim = fail and not r.full then newim := r.tryA2(20000); fi;
         if not newim = fail then
            Info(InfoIdp5, 2, "p5id_iso_random_bruteforce: case A2 for ",id);
            return newim;
         fi;
      fi;
   fi;

   ## ---------------------------------------------------------------------------
   ## (A3) class 2 with |Phi(G)| = p^2 and |G'| = p; then Phi(G) <= Z(G) and rank 3.
   ## The invariants on V = G/Phi(G) are the commutator form b: V x V --> G' (alternating
   ## of rank 2) and the p-power map pi: V --> Phi/G'. An isomorphism scales Phi/G' by mu
   ## and G' by nu, where nu = mu if Phi is cyclic and mu,nu are independent otherwise,
   ## and alpha satisfies b'(alpha x,alpha y) = nu*b(x,y) and pi'(alpha x) = mu*pi(x).
   ## In a basis x,y,z of V with b(x,y) = 1 and z spanning rad(b), such an alpha is built
   ## directly, so candidates arise without rejection. The lift uses r.liftu for an
   ## elementary abelian Phi(H) and r.liftcyc (equations over Z/p^2) for a cyclic one.
   ## ---------------------------------------------------------------------------
   ##
   r.graded2 := function(X)
      local Ph, Xd, nV, V, f, li, u, nU, U, cu, cc, dat, i, j, pos, bas;
      Ph := FrattiniSubgroup(X);
      Xd := DerivedSubgroup(X);
      nV := NaturalHomomorphismByNormalSubgroup(X, Ph);
      V  := Image(nV);   f := Pcgs(V);
      if not Length(f) = 3 then return fail; fi;
      li := u -> PreImagesRepresentative(nV, u);
      u  := First(AsList(Ph), z -> Order(z) = p^2);          ## Phi cyclic
      if u = fail then
         u := First(AsList(Ph), z -> not z in Xd and not IsOne(z));
      fi;
      if u = fail then return fail; fi;
      nU := NaturalHomomorphismByNormalSubgroup(Ph, Xd);       ## Phi --> Phi/G'
      U  := Image(nU);
      cu := z -> r.one*ExponentsOfPcElement(Pcgs(U), Image(nU, z))[1];
      cc := z -> r.one*ExponentsOfPcElement(Pcgs(Xd), z)[1];
      dat := rec(Ph := Ph, nat := nV, V := V, f := f, u := u, m := 3,
                 cyc := Order(u) = p^2);
      ## the coordinates are taken with respect to u mod G' and to a generator of G';
      ## for a cyclic Phi that generator has to be u^p, which is what ties nu to mu
      if dat.cyc then dat.c0 := u^p; else dat.c0 := Pcgs(Xd)[1]; fi;
      dat.b  := List([1..3], i -> List([1..3],
                       j -> cc(Comm(li(f[i]), li(f[j])))/cc(dat.c0)));
      dat.pi := List([1..3], i -> cu(li(f[i])^p)/cu(u));
      if IsZero(dat.pi) then return fail; fi;
       ## for an elementary abelian Phi = <u> x G' the p-power map has a second component
       ## rho in G', a further invariant: rho'(alpha v) = la*pi(v) + nu*rho(v), with one
       ## unknown scalar la
      if dat.cyc then
         dat.rho := fail;
      else
         bas := [ExponentsOfPcElement(Pcgs(Ph), u),
                 ExponentsOfPcElement(Pcgs(Ph), dat.c0)];
         bas := (r.one*bas)^-1;
         dat.rho := List([1..3], i -> ((r.one*ExponentsOfPcElement(Pcgs(Ph),
                            li(f[i])^p))*bas)[2]);
      fi;
      ## a basis x,y,z of V with b(x,y) = 1 and z spanning rad(b)
      if not Length(NullspaceMat(dat.b)) = 1 then return fail; fi;
      dat.z   := NullspaceMat(dat.b)[1];
      pos     := First(Cartesian([1..3],[1..3]), q -> not IsZero(dat.b[q[1]][q[2]]));
      dat.x   := List([1..3], i -> r.one*0);   dat.x[pos[1]] := r.one;
      dat.y   := List([1..3], i -> r.one*0);
      dat.y[pos[2]] := dat.b[pos[1]][pos[2]]^-1;
      dat.P   := [dat.x, dat.y, dat.z];
      if IsZero(DeterminantMat(dat.P)) then return fail; fi;
      dat.Pi  := dat.P^-1;
      return dat;
   end;

   ## r.rsol(rows,vals): a random solution Y of the system Y*rows[j] = vals[j], or fail
   r.rsol := function(rows, vals)
      local mt, sol, w;
      mt  := TransposedMat(rows);
      sol := SolutionMat(mt, vals);
      if sol = fail then return fail; fi;
      for w in NullspaceMat(mt) do sol := sol + Random(GF(p))*w; od;
      return sol;
   end;

   ## r.cand2(dG,dH): a random candidate alpha for (A3), as a 3x3 matrix over GF(p)
   r.units := Filtered(AsList(GF(p)), x -> not IsZero(x));

   r.cand2 := function(dG, dH)
      local mu, nu, la, X, Y, a, s, t, tv, A;
      mu := Random(r.units);
      if dG.cyc then nu := mu; else nu := Random(r.units); fi;
      if dG.rho = fail then
         la := fail;
         a  := r.scal(dH.z*dH.pi, mu*(dG.z*dG.pi));
         if a = fail then return fail; fi;
      else
         ## the two conditions on the image a*z' of z determine a and, with it, la
         s := dH.z*dH.pi;   t := dH.z*dH.rho;
         if not IsZero(dG.z*dG.pi) then
            a := r.scal(s, mu*(dG.z*dG.pi));
            if a = fail then return fail; fi;
            la := (a*t - nu*(dG.z*dG.rho))/(dG.z*dG.pi);
         else
            if not IsZero(s) then return fail; fi;
            la := Random(AsList(GF(p)));
            a  := r.scal(t, nu*(dG.z*dG.rho));
            if a = fail then return fail; fi;
         fi;
      fi;
      if IsZero(a) then return fail; fi;
      if la = fail then
         X := r.rsol([dH.pi], [mu*(dG.x*dG.pi)]);
         if X = fail then return fail; fi;
         Y := r.rsol([dH.pi, X*dH.b], [mu*(dG.y*dG.pi), nu]);
      else
         X := r.rsol([dH.pi, dH.rho],
                 [mu*(dG.x*dG.pi), la*(dG.x*dG.pi) + nu*(dG.x*dG.rho)]);
         if X = fail then return fail; fi;
         Y := r.rsol([dH.pi, dH.rho, X*dH.b],
                 [mu*(dG.y*dG.pi), la*(dG.y*dG.pi) + nu*(dG.y*dG.rho), nu]);
      fi;
      if Y = fail then return fail; fi;
      A := dG.Pi*[X, Y, a*dH.z];
      if IsZero(DeterminantMat(A)) then return fail; fi;
      return A;
   end;

   ## r.scal(s,t): a solution a of a*s = t, a random nonzero one if s and t vanish
   r.scal := function(s, t)
      if not IsZero(s) then return t/s; fi;
      if not IsZero(t) then return fail; fi;
      return Random(r.units);
   end;

   ## r.mkdlog(u): the discrete logarithm table of the cyclic group <u> of order p^2
   r.mkdlog := function(u)
      local D, i;
      D := NewDictionary(r.oneH, true);
      for i in [0..p^2-1] do AddDictionary(D, u^i, i); od;
      return D;
   end;

   ## r.cycprep(): the parts of the equations over Z/p^2 that do not depend on the
   ## images, namely the kernel of the system modulo p and its effect on the residual
   r.cycprep := function()
      local kb, dl, k, l, num, del;
      r.ker := NullspaceMat(r.mat);
      r.del := [];
      for kb in r.ker do
         dl  := List(kb, IntFFE);
         del := [];
         for k in [1..r.nrel] do
            num := -Sum([1..r.n], l -> r.exp[k][l]*dl[l]);
            if r.rel[k][2] = 0 then num := num + p*dl[r.rel[k][1]]; fi;
            Add(del, num/p);
         od;
         Add(r.del, del);
      od;
      r.amat := List(r.del,
                   del -> List(r.left,
                      t -> Sum([1..r.nrel], k -> t[k]*(r.one*del[k]))));
   end;

   ## r.cycres(om,ga): the residual (om - E*ga)/p of the system modulo p^2, or fail
   r.cycres := function(om, ga)
      local out, k, l, num;
      out := [];
      for k in [1..r.nrel] do
         num := om[k] - Sum([1..r.n], l -> r.exp[k][l]*ga[l]);
         if r.rel[k][2] = 0 then num := num + p*ga[r.rel[k][1]]; fi;
         if not num mod p = 0 then return fail; fi;
         Add(out, num/p);
      od;
      return out;
   end;

   ## r.liftcyc(im,u): lift through the central cyclic kernel <u> of order p^2. With the
   ## corrections written as u^gamma the relations read sum_l exp[k][l]*gamma_l -
   ## p*gamma_i = omega_k mod p^2 (the second term only for the power relation of i).
   ## Modulo p this is the system of r.liftu, so r.test applies; the solution is then
   ## corrected inside its kernel so that the second order part becomes solvable too.
   r.liftcyc := function(im, u)
      local om, k, l, w, v, cond, ga, rho, s, i, g1, c, hom;
      if not IsBound(r.amat) then r.cycprep(); fi;
      om := [];
      for k in [1..r.nrel] do
         if r.rel[k][2] = 0 then
            w := im[r.rel[k][1]]^p;
         else
            w := Comm(im[r.rel[k][2]], im[r.rel[k][1]]);
         fi;
         v := r.oneH;
         for l in r.sup[k] do v := v * im[l]^r.exp[k][l]; od;
         w := LookupDictionary(r.dlog, LeftQuotient(v, w));
         if w = fail then return fail; fi;
         Add(om, w);
         for cond in r.test[k] do
            if not IsZero(Sum(cond.sup, l -> cond.v[l]*(r.one*om[l]))) then
               return fail;
            fi;
         od;
      od;
      ga := SolutionMat(r.mat, r.one*om);
      if ga = fail then return fail; fi;
      ga  := List(ga, IntFFE);
      rho := r.cycres(om, ga);
      if rho = fail then return fail; fi;
      s := SolutionMat(r.amat,
              List(r.left, t -> -Sum([1..r.nrel], k -> t[k]*(r.one*rho[k]))));
      if s = fail then return fail; fi;
      for i in [1..Length(r.ker)] do
         ga := ga + IntFFE(s[i])*List(r.ker[i], IntFFE);
      od;
      rho := r.cycres(om, ga);
      if rho = fail then return fail; fi;
      g1 := SolutionMat(r.mat, r.one*rho);
      if g1 = fail then return fail; fi;
      c   := List([1..r.n], l -> u^((ga[l] + p*IntFFE(g1[l])) mod p^2));
      hom := GroupHomomorphismByImages(G, H, AsList(r.pcgG),
                   List([1..r.n], l -> im[l]*c[l]));
      if hom = fail or not IsBijective(hom) then return fail; fi;
      return hom;
   end;

   if NilpotencyClassOfGroup(G) = 2 and Size(FrattiniSubgroup(G)) = p^2
      and Size(DerivedSubgroup(G)) = p then
      r.dG2 := r.graded2(G);
      r.dH2 := r.graded2(H);
      if not (r.dG2 = fail or r.dH2 = fail) and r.dG2.cyc = r.dH2.cyc then
         if r.dH2.cyc then r.dlog := r.mkdlog(r.dH2.u); fi;
         ## the coordinates of the generators of G in V
         r.cG := List(r.pcgG, x -> r.one*ExponentsOfPcElement(r.dG2.f,
                         Image(r.dG2.nat, x)));
         r.tryA3 := function(tot)
            local i, A, im, new;
            for i in [1..tot] do
               ## a draw of the scalars can be inconsistent; that discards this
               ## candidate only, not the whole case
               A := r.cand2(r.dG2, r.dH2);
               if A = fail then continue; fi;
               im := List(r.cG, v -> PcElementByExponents(r.dH2.f,
                             List(v*A, IntFFE)));
               if r.dH2.cyc then
                  new := r.liftcyc(List(im, y -> PreImagesRepresentative(r.dH2.nat, y)),
                            r.dH2.u);
               else
                  new := r.liftu(im, r.dH2.nat, r.dH2.Ph);
               fi;
               if not new = fail then return new; fi;
            od;
            return fail;
         end;
         newim := r.tryA3(20000);
         if not newim = fail then
            Info(InfoIdp5, 2, "p5id_iso_random_bruteforce: case A3 for ",id);
            return newim;
         fi;
      fi;
   fi;

   ## ---------------------------------------------------------------------------
   ## (A4) two generator groups with Phi(G) = G' elementary abelian of order p^3. Then
   ## V = G/Phi(G) has dimension 2 and Phi/gamma_3 is canonically the exterior square of
   ## V, so with the generator w0 = [e1,e2] an isomorphism acts on it by det(alpha).
   ## Everything else is measured against w0: with t0 = [w0,e_j] and s0 = [t0,e_k] the
   ## scalars on gamma_3/gamma_4 and gamma_4 are tau = det(alpha)*q2'(alpha e_j) and
   ## sigma = tau*q3'(alpha e_k), where q2,q3 are the forms v -> [w0,v] and v -> [t0,v];
   ## the p-power map is matched layer by layer with the corresponding scalar. For class
   ## 4 this leaves a handful of candidates. For class 3 the graded Lie ring is free, so
   ## the brackets give no condition, but gamma_3 is then canonically V and the p-power
   ## map becomes an endomorphism Theta of V with Theta'*alpha = det(alpha)*alpha*Theta,
   ## which again leaves about p candidates. Each is lifted with kernel Phi(H).
   ## ---------------------------------------------------------------------------
   ##
   r.graded4 := function(X)
      local Ph, lc, cl, nV, V, f, li, g3, g4, nW, W, w, cw, n3, c3, c4, t, dat, i, j,
            bas, co;
      Ph := FrattiniSubgroup(X);   lc := LowerCentralSeries(X);
      cl := Length(lc)-1;
      if not cl in [3,4] then return fail; fi;
      nV := NaturalHomomorphismByNormalSubgroup(X, Ph);
      V  := Image(nV);   f := Pcgs(V);
      if not Length(f) = 2 then return fail; fi;
      li := u -> PreImagesRepresentative(nV, u);
      g3 := lc[3];
      nW := NaturalHomomorphismByNormalSubgroup(Ph, g3);
      W  := Image(nW);
      w  := Comm(li(f[1]), li(f[2]));            ## the canonical generator of Phi/gamma_3
      if Image(nW, w) = One(W) then return fail; fi;
      cw := z -> r.one*ExponentsOfPcElement(Pcgs(W), Image(nW, z))[1]
                  /(r.one*ExponentsOfPcElement(Pcgs(W), Image(nW, w))[1]);
      dat := rec(Ph := Ph, nat := nV, V := V, f := f, cl := cl, w0 := w);
      dat.q1 := List([1..2], i -> cw(li(f[i])^p));       ## p-power map modulo gamma_3
      if cl = 3 then
         ## gamma_3 is identified with V by v -> [w0,v]
         dat.F := List([1..2], i -> r.one*ExponentsOfPcElement(Pcgs(g3),
                            Comm(w, li(f[i]))));
         if IsZero(DeterminantMat(dat.F)) then return fail; fi;
         dat.Pw := List([1..2], i -> r.one*ExponentsOfPcElement(Pcgs(g3),
                            li(f[i])^p));
         dat.Th := dat.Pw*dat.F^-1;
         return dat;
      fi;
      ## class 4
      g4 := lc[4];
      n3 := NaturalHomomorphismByNormalSubgroup(g3, g4);
      c3 := z -> r.one*ExponentsOfPcElement(Pcgs(Image(n3)), Image(n3, z))[1];
      dat.j := First([1..2], i -> not Comm(w, li(f[i])) in g4);
      if dat.j = fail then return fail; fi;
      t  := Comm(w, li(f[dat.j]));                       ## the generator t0 of gamma_3/gamma_4
      dat.q2 := List([1..2], i -> c3(Comm(w, li(f[i])))/c3(t));
      dat.k  := First([1..2], i -> not IsOne(Comm(t, li(f[i]))));
      if dat.k = fail then return fail; fi;
      c4 := z -> r.one*ExponentsOfPcElement(Pcgs(g4), z)[1]
                  /(r.one*ExponentsOfPcElement(Pcgs(g4), Comm(t, li(f[dat.k])))[1]);
      dat.q3 := List([1..2], i -> c4(Comm(t, li(f[i]))));
      ## w0, t0 and s0 are a basis of the elementary abelian group Phi, so the p-power
      ## map can be read off in all three layers at once
      bas := (r.one*[ExponentsOfPcElement(Pcgs(Ph), w),
                     ExponentsOfPcElement(Pcgs(Ph), t),
                     ExponentsOfPcElement(Pcgs(Ph), Comm(t, li(f[dat.k])))])^-1;
      if bas = fail then return fail; fi;
      co := List([1..2],
               i -> (r.one*ExponentsOfPcElement(Pcgs(Ph), li(f[i])^p))*bas);
      dat.q1 := List(co, v -> v[1]);
      dat.q4 := List(co, v -> v[2]);
      dat.q5 := List(co, v -> v[3]);
      ## for v with q2(v) = q3(v) = 0 the commutator [w0,v] lies in gamma_4 already, and
      ## its value there is one more invariant: det(alpha)*lam'(alpha v) = sigma*lam(v)
      dat.lam := function(v)
         return c4(Comm(w, li(PcElementByExponents(f, List(v, IntFFE)))));
      end;
      return dat;
   end;

   ## r.spanres(v,sp): residuals that vanish exactly if the vector v lies in the span
   ## of the list sp; they are linear in v
   r.spanres := function(v, sp)
      if sp = [] then return v; fi;
      if Length(sp) = 1 then
         return [v[1]*sp[1][2] - v[2]*sp[1][1]];
      fi;
      if RankMat(sp) >= 2 then return []; fi;
      return [v[1]*sp[1][2] - v[2]*sp[1][1]];
   end;

   ## r.res4(A,dG,dH): residuals of the conditions of (A4) for a class 4 candidate. The
   ## p-power map is matched layer by layer, in each layer only up to the span of the
   ## forms of the previous layers, which is the freedom of the unknown deeper parts.
   r.res4 := function(A, dG, dH)
      local dt, tau, sig, out, sp, sc;
      dt  := DeterminantMat(A);
      tau := dt*(A[dG.j]*dH.q2);
      sig := tau*(A[dG.k]*dH.q3);
      out := ShallowCopy(A*dH.q2 - (A[dG.j]*dH.q2)*dG.q2);
      Append(out, A*dH.q3 - (A[dG.k]*dH.q3)*dG.q3);
      sp  := [];
      if not (IsZero(dG.q1) and IsZero(dH.q1)) then
         Append(out, A*dH.q1 - dt*dG.q1);
         Add(sp, dG.q1);
      fi;
      if not (IsZero(dG.q4) and IsZero(dH.q4)) then
         Append(out, r.spanres(A*dH.q4 - tau*dG.q4, sp));
         Add(sp, dG.q4);
      fi;
      if not (IsZero(dG.q5) and IsZero(dH.q5)) then
         Append(out, r.spanres(A*dH.q5 - sig*dG.q5, sp));
      fi;
      ## the second order commutator form on the canonical line
      if not (r.lG4 = fail or r.lH4 = fail) then
         sc := (r.u1G4*A)[r.c4]/r.u1H4[r.c4];
         Add(out, dt*sc*r.lH4 - sig*r.lG4);
      fi;
      return out;
   end;

   ## r.solveq(f0,f1,f2): the set of x in GF(p) with F(x) = 0, where F is a vector of
   ## polynomials of degree at most 2 given by its values at 0, 1 and 2
   r.solveq := function(f0, f1, f2)
      local all, res, k, c0, c1, c2, di, w;
      all := AsList(GF(p));   res := fail;
      for k in [1..Length(f0)] do
         c0 := f0[k];
         c2 := (f2[k] - 2*f1[k] + c0)/(r.one*2);
         c1 := f1[k] - c0 - c2;
         if IsZero(c2) and IsZero(c1) then
            if not IsZero(c0) then return []; fi;
            continue;
         elif IsZero(c2) then
            w := [-c0/c1];
         else
            di := c1^2 - 4*c2*c0;
            if IsZero(di) then
               w := [-c1/(2*c2)];
            else
               di := RootFFE(GF(p), di, 2);
               if di = fail then return []; fi;
               w := [(-c1+di)/(2*c2), (-c1-di)/(2*c2)];
            fi;
         fi;
         if res = fail then res := w; else res := Filtered(res, x -> x in w); fi;
         if res = [] then return []; fi;
      od;
      if res = fail then return all; fi;
      return res;
   end;

   ## r.cands4(dG,dH): the candidates for alpha in (A4), or fail if there are too many
   r.cands4 := function(dG, dH)
      local res, cap, ker, u1G, u2G, u1H, u2H, PG, PH, s, t, A, d, ns, i, j,
            e, u, v, c, dt, M, row, pts;
      cap := 300000;   res := [];
      if not dG.cl = dH.cl then return []; fi;
      if dG.cl = 3 then
         ## the intertwining condition alpha*Theta' = det(alpha)*Theta*alpha, written as
         ## a homogeneous system in the four entries of alpha for each value of det
         for d in r.units do
            M := [];
            for i in [1..2] do
               for j in [1..2] do                      ## the unknown alpha[i][j]
                  row := [];
                  for t in [1..2] do
                     for u in [1..2] do                ## the equation in position (t,u)
                        c := Zero(GF(p));
                        if i = t then c := c + dH.Th[j][u]; fi;
                        if j = u then c := c - d*dG.Th[t][i]; fi;
                        Add(row, c);
                     od;
                  od;
                  Add(M, row);
               od;
            od;
            ns := NullspaceMat(M);
            if ns = [] then continue; fi;
            ## det(alpha) = d fixes the scalar factor, so the projective points of the
            ## space of intertwiners suffice; a sample if that space is large
            pts := [];
            if Length(ns) <= 2 then
               for i in [1..Length(ns)] do
                  for e in Tuples(AsList(GF(p)), Length(ns)-i) do
                     v := ShallowCopy(ns[i]);
                     for t in [1..Length(ns)-i] do v := v + e[t]*ns[i+t]; od;
                     Add(pts, v);
                  od;
               od;
            else
               for i in [1..100] do
                  v := ns[1]*Zero(GF(p));
                  for t in [1..Length(ns)] do v := v + Random(GF(p))*ns[t]; od;
                  Add(pts, v);
               od;
            fi;
            for v in pts do
               A  := [v{[1,2]}, v{[3,4]}];
               dt := DeterminantMat(A);
               if IsZero(dt) then continue; fi;
               c := RootFFE(GF(p), d/dt, 2);
               if c = fail then continue; fi;
               A := c*A;
               if not IsZero(dG.q1) and not A*dH.q1 = d*dG.q1 then continue; fi;
               Add(res, A);   Add(res, -A);
               if Length(res) > cap then return fail; fi;
            od;
         od;
         return Permuted(res, Random(SymmetricGroup(Length(res))));
      fi;
      return [];            ## class 4 is handled by r.mats4, one pair (s,t) at a time
   end;

   ## r.base4(dG,dH): the bases adapted to the kernels of q2 and q2'
   r.base4 := function(dG, dH)
      local ker, u1G, u1H, u2G, u2H;
      ker := q -> [q[2], -q[1]];
      u1G := ker(dG.q2);   u1H := ker(dH.q2);
      u2G := First([[r.one, r.one*0], [r.one*0, r.one]],
                v -> not IsZero(u1G[1]*v[2]-u1G[2]*v[1]));
      u2H := First([[r.one, r.one*0], [r.one*0, r.one]],
                v -> not IsZero(u1H[1]*v[2]-u1H[2]*v[1]));
      return rec(PG := [u1G, u2G]^-1, PH := [u1H, u2H]);
   end;

   ## r.mats4(s,t,dG,dH): the class 4 candidates alpha = [[s,0],[a,t]] in the adapted
   ## basis; for fixed s,t the conditions have degree at most 2 in a, so a is solved for
   r.mats4 := function(s, t, dG, dH)
      local mat, A, c;
      mat := c -> r.bs4.PG*[[s, Zero(GF(p))], [c, t]]*r.bs4.PH;
      A   := List([0,1,2], c -> r.res4(mat(r.one*c), dG, dH));
      return List(r.solveq(A[1], A[2], A[3]), c -> mat(c));
   end;

   if Size(FrattiniSubgroup(G)) = p^3 and IsElementaryAbelian(FrattiniSubgroup(G))
      and FrattiniSubgroup(G) = DerivedSubgroup(G) then
      r.dG4 := r.graded4(G);
      r.dH4 := r.graded4(H);
      if not (r.dG4 = fail or r.dH4 = fail) then
         r.PhH := FrattiniSubgroup(H);
         r.wf2 := r.mkwf(r.PhH);
         r.fH4 := Pcgs(r.dH4.V);
         r.cG  := List(r.pcgG, x -> r.one*ExponentsOfPcElement(r.dG4.f,
                          Image(r.dG4.nat, x)));
         r.tryA4 := function()
            local cd, t, im, new, pairs, q, A;
            ## only a fraction of the candidates lifts, so they are tried in random
            ## order and produced only as far as they are needed
            if r.dG4.cl = 3 then
               cd := r.cands4(r.dG4, r.dH4);
               if cd = fail then return fail; fi;
               Info(InfoIdp5, 3, "p5id_iso_random_bruteforce: (A4) ",
                    Length(cd), " candidates");
            else
               r.bs4 := r.base4(r.dG4, r.dH4);
               ## the canonical line and the second order commutator form on it; the
               ## form is only canonical when the kernels of q2 and q3 agree
               r.lG4 := fail;   r.lH4 := fail;
               r.u1G4 := (r.bs4.PG^-1)[1];   r.u1H4 := r.bs4.PH[1];
               r.c4   := First([1..2], i -> not IsZero(r.u1H4[i]));
               if IsZero(r.dG4.q2[1]*r.dG4.q3[2]-r.dG4.q2[2]*r.dG4.q3[1]) then
                  r.lG4 := r.dG4.lam(r.u1G4);
                  r.lH4 := r.dH4.lam(r.u1H4);
                  if IsZero(r.lG4) and IsZero(r.lH4) then
                     r.lG4 := fail;   r.lH4 := fail;
                  fi;
               fi;
               cd    := fail;
            fi;
            if cd = fail then
               ## the pairs (s,t) are taken in random order, but the candidates of a
               ## batch are mixed before they are tried: the ones that lift sit in few pairs
               pairs := Cartesian(r.units, r.units);
               pairs := Permuted(pairs, Random(SymmetricGroup(Length(pairs))));
            else
               pairs := [];
            fi;
            A := cd;
            for q in [1..Length(pairs)+1] do
               if q <= Length(pairs) then
                  if A = fail then A := []; fi;
                  Append(A, r.mats4(pairs[q][1], pairs[q][2], r.dG4, r.dH4));
                  if Length(A) < 3000 and q < Length(pairs) then continue; fi;
               elif A = fail then
                  return fail;
               fi;
               for t in Permuted(A, Random(SymmetricGroup(Length(A)))) do
                  im := List(r.cG, v -> PreImagesRepresentative(r.dH4.nat,
                                PcElementByExponents(r.fH4, List(v*t, IntFFE))));
                  new := r.liftmodu(im, r.PhH, r.wf2);
                  if not new = fail then return new; fi;
               od;
               A := [];
               if q > Length(pairs) then return fail; fi;
            od;
            return fail;
         end;
         newim := r.tryA4();
         if not newim = fail then
            Info(InfoIdp5, 2, "p5id_iso_random_bruteforce: case A4 for ",id);
            return newim;
         fi;
      fi;
   fi;

   ## ---------------------------------------------------------------------------
   ## (A5) the remaining two generator groups, where Phi(G) is not elementary abelian or
   ## is larger than G'. With D = Phi^p*[Phi,G] and U = Phi/D both the p-power map
   ## pi: V --> U and the commutator b = [e1,e2] in U are canonical, and an isomorphism
   ## induces beta on U with beta*pi = pi'*alpha and beta(b) = det(alpha)*b'. Hence alpha
   ## maps ker(pi) to ker(pi'), and if pi is injective with b = pi(v0), then
   ## alpha(v0) = det(alpha)*v0'. Deeper conditions come from D (r.res5). The candidates
   ## are lifted through Phi(H), which may have exponent p^2 (r.liftab); modulo D the
   ## equations again have the matrix r.exp, so r.test rejects most of them at once.
   ## ---------------------------------------------------------------------------
   ##
   r.graded5 := function(X)
      local Ph, D, nU, U, fu, nV, V, fv, li, dat, i, j, D2, nL, L,
            nA, A, U1, U2, U3, n1, n2, x, g1, g2, c1, c2, cb;
      Ph := FrattiniSubgroup(X);
      nV := NaturalHomomorphismByNormalSubgroup(X, Ph);
      V  := Image(nV);   fv := Pcgs(V);
      if not Length(fv) = 2 then return fail; fi;
      li := u -> PreImagesRepresentative(nV, u);
      D  := ClosureGroup(Agemo(Ph, p), CommutatorSubgroup(Ph, X));
      nU := NaturalHomomorphismByNormalSubgroup(Ph, D);
      U  := Image(nU);   fu := Pcgs(U);
      dat := rec(Ph := Ph, nat := nV, V := V, f := fv, D := D, U := U, m := Length(fu),
                 li := li, expp := Exponent(Ph) = p);
      dat.pi := List([1..2], i -> r.one*ExponentsOfPcElement(fu,
                          Image(nU, li(fv[i])^p)));
      dat.b  := r.one*ExponentsOfPcElement(fu, Image(nU, Comm(li(fv[1]), li(fv[2]))));
      if dat.m = 0 then dat.rk := 0; else dat.rk := RankMat(dat.pi); fi;
      ## v0 with pi(v0) = b, if b lies in the image of an injective pi
      dat.v0 := fail;
      if dat.rk = 2 then dat.v0 := SolutionMat(dat.pi, dat.b); fi;
      ## for class 2 the p-power map is a homomorphism, so X/X' has a canonical filtration
      ## by p-th powers; if its layers are 1-dimensional, then the forms tau_k(v) =
      ## v^(p^k) are canonical and, with generators chosen as p-th powers of each other,
      ## an isomorphism scales all of them by the SAME scalar m
      dat.tau := fail;
      if NilpotencyClassOfGroup(X) = 2 then
         nA := NaturalHomomorphismByNormalSubgroup(X, DerivedSubgroup(X));
         A  := Image(nA);
         U1 := Agemo(A, p, 1);   U2 := Agemo(A, p, 2);   U3 := Agemo(A, p, 3);
         if Size(U1)/Size(U2) = p and Size(U2)/Size(U3) = p then
            n1 := NaturalHomomorphismByNormalSubgroup(U1, U2);
            n2 := NaturalHomomorphismByNormalSubgroup(U2, U3);
            x  := First(List(fv, u -> Image(nA, li(u))),
                     y -> not y^p in U2 and not y^(p^2) in U3);
            if not x = fail then
               g1 := Image(n1, x^p);   g2 := Image(n2, x^(p^2));
               c1 := z -> r.one*ExponentsOfPcElement(Pcgs(Image(n1)), Image(n1, z))[1]
                           /(r.one*ExponentsOfPcElement(Pcgs(Image(n1)), g1)[1]);
               c2 := z -> r.one*ExponentsOfPcElement(Pcgs(Image(n2)), Image(n2, z))[1]
                           /(r.one*ExponentsOfPcElement(Pcgs(Image(n2)), g2)[1]);
               dat.tau := [List(fv, u -> c1(Image(nA, li(u))^p)),
                           List(fv, u -> c2(Image(nA, li(u))^(p^2)))];
            fi;
         fi;
      fi;
      ## the next layer: the canonical pairing mu: U x V --> D/(D^p*[D,X]), which is
      ## well defined because Phi is abelian. It is used through r.ok5.
      D2 := ClosureGroup(Agemo(D, p), CommutatorSubgroup(D, X));
      nL := NaturalHomomorphismByNormalSubgroup(D, D2);
      L  := Image(nL);
      dat.nL := nL;   dat.L := L;
      ## the p-power map on the kernel of pi, which lands in D when Phi has exponent p
      dat.kap := fail;
      if dat.expp and Length(Pcgs(L)) = 1 then
         dat.kap := function(v)
            local z;
            z := li(PcElementByExponents(fv, List(v, IntFFE)))^p;
            if not z in D then return fail; fi;
            return r.one*ExponentsOfPcElement(Pcgs(L), Image(nL, z))[1];
         end;
      fi;
      dat.mu  := fail;
      dat.rho := fail;
      if Length(Pcgs(L)) = 1 and dat.m > 0 then
         dat.mu := List([1..dat.m], i -> List([1..2],
            j -> r.one*ExponentsOfPcElement(Pcgs(L), Image(nL,
                    Comm(PreImagesRepresentative(nU, fu[i]), li(fv[j]))))[1]));
         if IsZero(dat.mu) then dat.mu := fail; fi;
         ## if D has exponent p, then u -> u^p is a well defined map U --> D/D2, with
         ## the same scalar as the pairing; that is one more condition
         if Exponent(D) = p then
            dat.rho := List([1..dat.m],
               i -> r.one*ExponentsOfPcElement(Pcgs(L), Image(nL,
                       PreImagesRepresentative(nU, fu[i])^p))[1]);
            if IsZero(dat.rho) then dat.rho := fail; fi;
         fi;
      fi;
      ## the second p-power layer as a form on V: y(v) = v^(p^2) in D/D2; if the
      ## commutator lies in D, then the scalar there is det(alpha)
      dat.y := fail;
      if not dat.rho = fail then
         dat.y := dat.pi*dat.rho;
         if IsZero(dat.y) then dat.y := fail; fi;
      fi;
      dat.b0 := dat.m > 0 and IsZero(dat.b)
                  and not IsOne(Comm(li(fv[1]), li(fv[2])));
      if dat.b0 then
         ## then the commutator itself lies in D, and it is the right unit for the
         ## coordinates there: with respect to it the scalar of the layer is det(alpha)
         cb := r.one*ExponentsOfPcElement(Pcgs(L),
                  Image(nL, Comm(li(fv[1]), li(fv[2]))))[1];
         if IsZero(cb) then
            dat.b0 := false;
         else
            if not dat.rho = fail then dat.rho := dat.rho/cb; fi;
            if not dat.y   = fail then dat.y   := dat.y/cb;   fi;
         fi;
      fi;
      return dat;
   end;

   ## r.base5(dG,dH): bases of V and V' adapted to the canonical line of each side, and
   ## the shape of the candidates: "line", "vec" or "free" (no condition from this layer)
   r.base5 := function(dG, dH)
      local cmpl, mk, ker, u1G, u1H;
      cmpl := u -> First([[r.one, r.one*0], [r.one*0, r.one]],
                      v -> not IsZero(u[1]*v[2]-u[2]*v[1]));
      mk := function(kind, uG, uH)
         local PG, PH;
         if uG = fail or uH = fail or IsZero(uG) or IsZero(uH) then return fail; fi;
         PG := [uG, cmpl(uG)];   PH := [uH, cmpl(uH)];
         if IsZero(DeterminantMat(PG)) or IsZero(DeterminantMat(PH)) then
            return fail;
         fi;
         return rec(kind := kind, PG := PG^-1, PH := PH,
                    dd := DeterminantMat(PH)/DeterminantMat(PG));
      end;
      if not dG.rk = dH.rk then return fail; fi;
      ## the kernel of the p-power map, if it is a line
      if dG.rk = 1 and dG.m > 0 and dH.m > 0 then
         ker := d -> NullspaceMat(d.pi);
         if Length(ker(dG)) = 1 and Length(ker(dH)) = 1 then
            u1G := mk("line", ker(dG)[1], ker(dH)[1]);
            if not u1G = fail then return u1G; fi;
         fi;
      fi;
      ## if pi is injective and b lies in its image, then alpha(v0) = det(alpha)*v0'
      if dG.rk = 2 and not (dG.v0 = fail or dH.v0 = fail) then
         u1G := mk("vec", dG.v0, dH.v0);
         if not u1G = fail then return u1G; fi;
      fi;
      ## the kernel of the second p-power form, if there is one
      if not (dG.y = fail or dH.y = fail) then
         u1G := mk("line", [dG.y[2], -dG.y[1]], [dH.y[2], -dH.y[1]]);
         if not u1G = fail then return u1G; fi;
      fi;
      ## otherwise the right kernel of the canonical pairing, if it is a line
      if not (dG.mu = fail or dH.mu = fail) then
         ker := d -> NullspaceMat(TransposedMat(d.mu));
         if Length(ker(dG)) = 1 and Length(ker(dH)) = 1 then
            u1G := mk("line", ker(dG)[1], ker(dH)[1]);
            if not u1G = fail then return u1G; fi;
         fi;
      fi;
      return rec(kind := "free");
   end;

   ## r.tcands(dG,dH): the candidates from the p-power layers of (A5); the conditions
   ## are homogeneous in (alpha,m), so every nonzero solution is taken
   r.tcands := function(dG, dH)
      local M, k, j, c, row, ns, d, v, t, A, res;
      M := [];
      for k in [1..Length(dG.tau)] do
         for j in [1..2] do
            row := List([1..5], c -> Zero(GF(p)));
            for c in [1..2] do row[2*(j-1)+c] := dH.tau[k][c]; od;
            row[5] := -dG.tau[k][j];
            Add(M, row);
         od;
      od;
      ns := NullspaceMat(TransposedMat(M));
      d  := Length(ns);
      ## the solution space is taken as a whole (its scalar multiples are different
      ## candidates); if it is too large, then the conditions are too weak to be useful
      if d = 0 or (p^d-1) > 12000 then return fail; fi;
      res := [];
      for t in Tuples(AsList(GF(p)), d) do
         v := ns[1]*Zero(GF(p));
         for k in [1..d] do v := v + t[k]*ns[k]; od;
         if IsZero(v[5]) then continue; fi;
         A := [v{[1,2]}, v{[3,4]}];
         if not IsZero(DeterminantMat(A)) then Add(res, A); fi;
      od;
      return res;
   end;

   ## r.linv(T,m): a left inverse of the 3 x m matrix T of rank m, or fail
   r.linv := function(T, m)
      local I, si, Tl, i, k;
      I := First(Combinations([1..3], m), c -> RankMat(T{c}) = m);
      if I = fail then return fail; fi;
      si := (T{I})^-1;
      Tl := List([1..m], i -> List([1..3], k -> Zero(GF(p))));
      for i in [1..m] do
         for k in [1..m] do Tl[i][I[k]] := si[i][k]; od;
      od;
      return Tl;
   end;

   ## r.res5(A,dG,dH): residuals of the conditions from the layer D/D2. Here beta is
   ## determined by beta*pi = pi'*alpha and beta(b) = det(alpha)*b', and the pairing with
   ## V, the p-power map on U, the form y and the p-power map on the canonical line must
   ## all be preserved with ONE common scalar, read off from the pairing or equal to
   ## det(alpha). All residuals have degree at most 2 in each entry of A.
   r.res5 := function(A, dG, dH)
      local T, S, be, w, v, sc, cnum, cden, out, i, j;
      if r.Tl5 = fail then return []; fi;
      T   := Concatenation(dG.pi, [dG.b]);
      S   := Concatenation(A*dH.pi, [DeterminantMat(A)*dH.b]);
      be  := r.Tl5*S;
      out := Concatenation(T*be - S);
      cnum := fail;   cden := r.one;
      if not (dG.mu = fail or dH.mu = fail) then
         w    := be*dH.mu*TransposedMat(A);
         cnum := w[r.pos5[1]][r.pos5[2]];
         cden := dG.mu[r.pos5[1]][r.pos5[2]];
         for i in [1..dG.m] do
            for j in [1..2] do
               Add(out, w[i][j]*cden - cnum*dG.mu[i][j]);
            od;
         od;
      elif dG.b0 and dH.b0 then
         cnum := DeterminantMat(A);
      fi;
      if cnum = fail then return out; fi;
      if not (dG.rho = fail or dH.rho = fail) then
         v := be*dH.rho;
         for i in [1..dG.m] do Add(out, v[i]*cden - cnum*dG.rho[i]); od;
      fi;
      if not (dG.y = fail or dH.y = fail) then
         v := A*dH.y;
         for j in [1..2] do Add(out, v[j]*cden - cnum*dG.y[j]); od;
      fi;
      if not (r.kG5 = fail or r.kH5 = fail) then
         sc := (r.u1G5*A)[r.c5]/r.u1H5[r.c5];
         Add(out, sc*r.kH5*cden - cnum*r.kG5);
      fi;
      return out;
   end;

   ## r.ok5(A,dG,dH): the same conditions as a test, including that alpha is invertible
   r.ok5 := function(A, dG, dH)
      if IsZero(DeterminantMat(A)) then return false; fi;
      if r.Tl5 = fail then return true; fi;
      return IsZero(r.res5(A, dG, dH));
   end;

   if Size(FrattiniSubgroup(G)) = p^3 and IsAbelian(FrattiniSubgroup(G))
      and not (IsElementaryAbelian(FrattiniSubgroup(G))
               and FrattiniSubgroup(G) = DerivedSubgroup(G)) then
      r.dG5 := r.graded5(G);
      r.dH5 := r.graded5(H);
      r.bs5 := fail;
      if not (r.dG5 = fail or r.dH5 = fail) then r.bs5 := r.base5(r.dG5, r.dH5); fi;
      if not (r.bs5 = fail or r.dG5 = fail or r.dH5 = fail) then
         r.PhH := FrattiniSubgroup(H);
         r.wf5 := r.mkwf(r.PhH);
         ## data for the conditions of the next layer
         r.Tl5  := fail;   r.pos5 := fail;
         if r.dG5.m > 0 then
            r.Tl5 := r.linv(Concatenation(r.dG5.pi, [r.dG5.b]), r.dG5.m);
            if not (r.dG5.mu = fail or r.dH5.mu = fail) then
               r.pos5 := First(Cartesian([1..r.dG5.m], [1..2]),
                            q -> not IsZero(r.dG5.mu[q[1]][q[2]]));
               if r.pos5 = fail then r.Tl5 := fail; fi;
            elif not (r.dG5.b0 and r.dH5.b0) then
               r.Tl5 := fail;
            fi;
         fi;
         ## the p-power map on the canonical line, if there is one
         r.kG5 := fail;   r.kH5 := fail;
         if r.bs5.kind = "line" and not (r.dG5.kap = fail or r.dH5.kap = fail) then
            r.u1G5 := (r.bs5.PG^-1)[1];   r.u1H5 := r.bs5.PH[1];
            r.c5   := First([1..2], i -> not IsZero(r.u1H5[i]));
            r.kG5  := r.dG5.kap(r.u1G5);
            r.kH5  := r.dH5.kap(r.u1H5);
            if r.kG5 = fail or r.kH5 = fail or (IsZero(r.kG5) and IsZero(r.kH5)) then
               r.kG5 := fail;   r.kH5 := fail;
            fi;
         fi;
         r.el5 := IsElementaryAbelian(r.PhH);
         r.fH5 := Pcgs(r.dH5.V);
         r.cG  := List(r.pcgG, x -> r.one*ExponentsOfPcElement(r.dG5.f,
                          Image(r.dG5.nat, x)));
         ## one candidate: the images in V', lifted through Phi(H)
         r.n5 := 0;
         ## without the conditions of the next layer the candidates are many, so the
         ## work is bounded and the general search takes over if nothing is found
         if r.Tl5 = fail then r.lim5 := 800; else r.lim5 := 2000; fi;
         r.try5 := function(A)
            local im;
            if r.n5 > r.lim5 then return fail; fi;
            if not r.ok5(A, r.dG5, r.dH5) then return fail; fi;
            r.n5 := r.n5 + 1;
            im := List(r.cG, v -> PreImagesRepresentative(r.dH5.nat,
                          PcElementByExponents(r.fH5, List(v*A, IntFFE))));
            if r.el5 then return r.liftmodu(im, r.PhH, r.wf5); fi;
            return r.liftab(im, r.PhH, r.wf5);
         end;
         r.tryA5 := function(tot)
            local cd, i, s, t, a, A, new, pairs, q;
            ## the p-power layers, if they are available, give the strongest conditions
            if not r.dG5.tau = fail and not r.dH5.tau = fail then
               cd := r.tcands(r.dG5, r.dH5);
               if not cd = fail then
                  Info(InfoIdp5, 3, "p5id_iso_random_bruteforce: (A5) ",
                       Length(cd), " candidates from the p-power layers");
                  for A in Permuted(cd, Random(SymmetricGroup(Length(cd)))) do
                     new := r.try5(A);
                     if not new = fail then return new; fi;
                  od;
               fi;
            fi;
            if r.bs5.kind = "free" then
               ## every alpha is admissible, so take them at random
               for i in [1..tot] do
                  new := r.try5(RandomInvertibleMat(2, GF(p)));
                  if not new = fail then return new; fi;
               od;
               return fail;
            fi;
            if r.bs5.kind = "vec" then
               ## alpha(v0) = det(alpha)*v0' forces the second diagonal entry
               cd := [];
               for s in r.units do
                  for a in AsList(GF(p)) do
                     Add(cd, r.bs5.PG*[[s, Zero(GF(p))], [a, r.bs5.dd^-1]]*r.bs5.PH);
                  od;
               od;
               for A in Permuted(cd, Random(SymmetricGroup(Length(cd)))) do
                  new := r.try5(A);
                  if not new = fail then return new; fi;
               od;
               return fail;
            fi;
            ## kind = "line": alpha = [[s,0],[a,t]] in the adapted basis; a is solved
            ## for if the next layer gives conditions, and run through otherwise
            pairs := Cartesian(r.units, r.units);
            pairs := Permuted(pairs, Random(SymmetricGroup(Length(pairs))));
            cd := [];
            for q in [1..Length(pairs)] do
               s := pairs[q][1];   t := pairs[q][2];
               if r.Tl5 = fail then
                  cd := Concatenation(cd, List(AsList(GF(p)),
                           a -> r.bs5.PG*[[s, Zero(GF(p))], [a, t]]*r.bs5.PH));
               else
                  A := List([0,1,2], a -> r.bs5.PG*[[s, Zero(GF(p))],
                                             [r.one*a, t]]*r.bs5.PH);
                  cd := Concatenation(cd, List(
                           r.solveq(r.res5(A[1], r.dG5, r.dH5),
                                    r.res5(A[2], r.dG5, r.dH5),
                                    r.res5(A[3], r.dG5, r.dH5)),
                           a -> r.bs5.PG*[[s, Zero(GF(p))], [a, t]]*r.bs5.PH));
               fi;
               if Length(cd) < 2000 and q < Length(pairs) then continue; fi;
               for A in Permuted(cd, Random(SymmetricGroup(Length(cd)))) do
                  new := r.try5(A);
                  if not new = fail then return new; fi;
               od;
               if r.n5 > r.lim5 then return fail; fi;
               cd := [];
            od;
            return fail;
         end;
         newim := r.tryA5(300);
         Info(InfoIdp5, 3, "p5id_iso_random_bruteforce: (A5) kind ", r.bs5.kind,
              ", ", r.n5, " candidates tried");
         if not newim = fail then
            Info(InfoIdp5, 2, "p5id_iso_random_bruteforce: case A5 for ",id);
            return newim;
         fi;
      fi;
   fi;

   ## ---------------------------------------------------------------------------
   ## (B) attempts: the admissible characteristic subgroups, smallest first
   ## ---------------------------------------------------------------------------
   r.cand  := r.chars(G);
   r.candH := r.chars(H);
   r.pos   := Filtered([1..Length(r.cand)], i -> Size(r.cand[i]) > 1);
   r.pos   := Filtered(r.pos, i -> not ForAny(r.pos, j -> j < i and r.cand[j] = r.cand[i]));
   SortBy(r.pos, i -> [Size(r.cand[i]), i]);
   r.qs := [];
   for k in r.pos do
      t := r.std(r.stdG(r.cand[k]), r.candH[k]);
      if t = fail then continue; fi;
      t.chr := true;            ## K is characteristic: a liftable isomorphism exists
      Add(r.qs, t);
      newim := r.lift(t.map, t.nat, t.natH, t.K);
      if not newim = fail then
         Info(InfoIdp5, 2, "p5id_iso_random_bruteforce: case B for ",id);
         return newim;
      fi;
   od;

   ## ---------------------------------------------------------------------------
   ## (B2) the subgroups of order p of C are not characteristic, so there is no canonical
   ## partner in H: we fix one of them in G and run over all p+1 subgroups of order p of
   ## CH, keep those with G/K and H/KH isomorphic, and try to lift. This is complete
   ## because an isomorphism maps C onto CH; the quotients are larger than G/C and carry
   ## more information, and p+1 lifts are much cheaper than the random search in (C).
   ## ---------------------------------------------------------------------------
   if Length(Pcgs(C)) = 2 then
      gen  := Pcgs(C);
      genH := Pcgs(CH);
      r.K  := Subgroup(G, [gen[1]]);
      r.gK := r.stdG(r.K);          ## the same for all candidates KH below
      for k in [0..p] do
         if k = p then
            r.KH := Subgroup(H, [genH[1]]);
         else
            r.KH := Subgroup(H, [genH[2]*genH[1]^k]);
         fi;
         t := r.std(r.gK, r.KH);
         if t = fail then continue; fi;
         t.chr := false;      ## K is not characteristic here, so this quotient need
                              ## not admit a liftable isomorphism at all
         Add(r.qs, t);        ## still a candidate for the random search in (C): these
                              ## quotients are larger, and their index is much smaller
         newim := r.lift(t.map, t.nat, t.natH, t.K);
         if not newim = fail then
            Info(InfoIdp5, 2, "p5id_iso_random_bruteforce: case B2 for ",id);
            return newim;
         fi;
      od;
   fi;

   ## ---------------------------------------------------------------------------
   ## (C) brute force. Some isomorphism G --> H exists and induces iso' = b*t.map on the
   ## quotient for some b in Aut(H/KH); since c*b*t.map lifts for every c in the image of
   ## Aut(H), the automorphisms that do the job form a coset of that image, and the
   ## expected number of random tries is its index. That index is out of reach for the
   ## groups still open here, so this is a bounded random search over all quotients
   ## collected in (B) and (B2), starting with the more promising ones. No orders of
   ## automorphism groups are computed; we only use that abelian quotients tend to have
   ## large automorphism groups and that large quotients are informative.
   ## ---------------------------------------------------------------------------
   if not r.qs = [] then
      ## all quotients from (B) and (B2) are used: those from (B2) are more promising
      ## (larger quotient, index smaller by about p), but only one of them lifts at all,
      ## so none may be dropped. For a characteristic K a liftable isomorphism is
      ## guaranteed to exist, for the others not; the former get half of the budget.
      SortBy(r.qs, x -> [not x.chr, IsAbelian(x.Q), -Size(x.Q)]);
      ## one try costs about 0.1 ms, essentially independent of p, so the total number
      ## r.tot of tries is a constant: roughly the seconds we are willing to spend times
      ## 5000. Raise it to trade time for coverage.
      r.tot := 10^6;
      r.nch := Number(r.qs, x -> x.chr);
      for t in r.qs do
         if t.chr then
            ## a liftable isomorphism is guaranteed here, so these quotients get the
            ## bulk of the budget
            itCH := QuoInt(r.tot, r.nch);
         else
            itCH := Maximum(50, QuoInt(r.tot, 5*(Length(r.qs)-r.nch)));
         fi;
         adj    := AutomorphismGroup(t.Q);
         r.gens := Concatenation(GeneratorsOfGroup(adj),
                                 List(GeneratorsOfGroup(adj), x -> x^-1));
         r.im   := List(r.pcgG, x -> Image(t.map, Image(t.nat, x)));
         for k in [1..itCH] do
            ## a few steps of a random walk on Aut(H/K), carried out on the images
            ## only; this avoids composing random automorphisms, which would dominate
            ## the cost. Consecutive tries have to be decorrelated, so one step is not
            ## enough; on the other hand the test below discards most candidates after
            ## one or two relations, so a long walk is not worth its price either.
            for j in [1..5] do
               r.g  := Random(r.gens);
               r.im := List(r.im, y -> Image(r.g, y));
            od;
            newim := r.liftu(r.im, t.natH, t.K);
            if not newim = fail then
               Info(InfoIdp5, 2, "p5id_iso_random_bruteforce: case C for ",id);
               return newim;
            fi;
         od;
      od;
   fi;


################################################################################# END OF CLAUDE CODE!!!!!


    return fail;

end );
