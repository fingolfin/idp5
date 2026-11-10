# Idp5

A GAP package for the identification of the groups of order dividing $p^5$,
for any prime $p$, with the groups in the SmallGroups library. It accompanies
the paper

  "Group identification for the groups of order dividing $p^5$"

by Heiko Dietrich, Bettina Eick, and Henrik Schanze.

The SmallGroups library contains all groups of order $p^5$, but its
identification function `IdGroup` is not available for order $p^5$ with
$p \geq 7$. Once the package is loaded, `IdSmallGroup` (equivalently `IdGroup`)
works for all groups of order $p^n$ with $n \leq 5$ and $p$ prime; for
$p = 2,3,5$ the methods of the SmallGroups library are used.

The package also provides the attribute `IsomorphismSmallGroup`: for a group
$G$ of order dividing $p^5$ it computes an isomorphism
$G\to \text{SmallGroup}(\text{IdSmallGroup}(G))$.

N.B.: for groups of order dividing $p^4$ the isomorphism is computed together
with the ID, and this algorithm always succeeds. For groups of order $p^5$, the
construction of the isomorphism reduces to the isomorphism problem for groups
of order dividing $p^4$ and considers lifts; this is partly randomised and the
implementation of this case has been developed with the LLM Claude Opus. Every
isomorphism returned is verified. While the search can in principle return
`fail`, this has not been observed in practice.

The final version of this package has been refactored, streamlined, and tested
with the help of Claude Pro.

## Installation

Unpack the archive in the `pkg` subdirectory of your GAP installation (or in
any other GAP package directory), and load the package with

```gap
gap> LoadPackage("idp5");
```

The package needs GAP 4.14 or later and the SmallGrp package; it suggests
the AutPGrp package. No compilation is needed.

## Example

```gap
gap> ### get random group
gap> R := SmallGroup(7^5,65);;
gap> R := Image(IsomorphismPermGroup(R));;
gap> repeat gens := List([1..8],x->Random(R)); until Group(gens)=R;;
gap> R := Group(gens);;
gap>
gap> ### construct ID
gap> IdSmallGroup(R);
[ 16807, 65 ]
gap>
gap> ### get iso to standard copy
gap> iso := IsomorphismSmallGroup(R);;
gap>
gap> ### Image(iso) is canonically isomorphic to H := SmallGroup(7^5,65):
gap> ### We have Image(iso) <> H, but mapping Pcgs(Image(iso))
gap> ### to Pcgs(SmallGroup(IdSmallGroup(R))) defines an isomorphism;
gap> ### demonstrate this:
gap> H := SmallGroup(7^5,65);;
gap> isoRtoH := iso * GroupHomomorphismByImages(Image(iso),H,Pcgs(Image(iso)),Pcgs(H));;
gap> Source(isoRtoH)=R and Image(isoRtoH)=H and IsBijective(isoRtoH);
true
```

## Public functions

* `IdSmallGroup(G)` / `IdGroup(G)`: a new method for groups of order $p^n$
  with $p > 5$ and $n \leq 5$.
* `IsomorphismSmallGroup(G)`: an isomorphism from $G$ onto
  `SmallGroup(IdSmallGroup(G))`, for groups of order $p^n$ with $n \leq 5$
  and any prime $p$; `fail` if the randomised search fails.
* `TypeFromIdSmallGroup_p5(p, i)` and `IdSmallGroupFromType_p5(p, type)`:
  for $p > 5$, the SmallGroups library constructs the groups of order $p^5$
  from 70 parametrised presentations ("types"); these functions convert
  between the IDs and the types `[t]` or `[t,k]`.
* `TestSmallGroupID_p5(lps, nr, testIso)`: a test function, see below.
* `InfoIdp5`: the info class of the package.

All other functions and variables are internal and start with `p5id_`.

## Tests

```gap
gap> TestPackage("idp5");
```

runs the test suite in `tst/` (about a minute): it identifies random copies
of all groups of order $p^n$, $n \leq 5$, for $p = 2,3,5,7,11,13,17$,
constructs the isomorphisms onto the library groups, and runs the examples of
the manual.

The test function `TestSmallGroupID_p5` takes as input a list `lps` of primes,
an integer `nr`, and a Boolean `testIso`; it will then run over `nr` copies
of the groups of order $p^i$ where $p$ lies in `lps` and $i = 1,2,3,4,5$
and tests that `IdSmallGroup` is computed correctly. If the Boolean `testIso`
is true, then it also tests the isomorphism construction. It outputs
statistics of the runtimes.

Example test:

```gap
gap> t := TestSmallGroupID_p5([37,61,101],1,true);;
------ start p = 37
ID [37^1,1] copy 1:   id 2 ms,  iso 0 ms
ID [37^2,1] copy 1:   id 1 ms,  iso 0 ms
ID [37^2,2] copy 1:   id 1 ms,  iso 0 ms
...
ID [101^5,267] copy 1:   id 1 ms,  iso 11 ms
ID [101^5,268] copy 1:   id 3 ms,  iso 31 ms
ID [101^5,269] copy 1:   id 1 ms,  iso 1 ms

------ summary
average time for ID: 51 ms   (607 tests)
ten largest runtimes for ID:
   273 ms   for SmallGroup(101^5,257)
   235 ms   for SmallGroup(101^5,256)
   187 ms   for SmallGroup(101^5,120)
   163 ms   for SmallGroup(101^5,121)
   157 ms   for SmallGroup(101^5,214)
   156 ms   for SmallGroup(101^5,149)
   154 ms   for SmallGroup(101^5,155)
   153 ms   for SmallGroup(101^5,199)
   153 ms   for SmallGroup(101^5,184)
   152 ms   for SmallGroup(101^5,234)
average time for iso: 71 ms   (607 tests)
ten largest runtimes for iso:
   3187 ms   for SmallGroup(101^5,125)
   1595 ms   for SmallGroup(101^5,119)
   1589 ms   for SmallGroup(101^5,121)
   1584 ms   for SmallGroup(101^5,120)
   1305 ms   for SmallGroup(101^5,259)
   1245 ms   for SmallGroup(61^5,85)
   1244 ms   for SmallGroup(101^5,262)
   897 ms   for SmallGroup(61^5,184)
   806 ms   for SmallGroup(101^5,258)
   694 ms   for SmallGroup(101^5,130)
wrong IDs: 0
isomorphism search failed: 0
returned map not an isomorphism: 0
```

## Files

```
PackageInfo.g, init.g, read.g
gap/idp5.gd       declarations of the public functions, text of the manual
gap/types.gi      TypeFromIdSmallGroup_p5, IdSmallGroupFromType_p5
gap/isop4.gi      identification and isomorphisms for order dividing p^4
gap/idp5.gi       identification for order p^5
gap/isop5.gi      isomorphisms for order p^5 (randomised lifting)
gap/methods.gi    the methods for IdSmallGroup and IsomorphismSmallGroup
gap/testing.gi    TestSmallGroupID_p5
tst/testall.g     runs the test suite
tst/idp5.tst      the tests
tst/idp501.tst    the examples of the manual (extracted by makedoc.g)
makedoc.g         builds the manual in doc/ (gap makedoc.g)
doc/              the manual (PDF, HTML, text); doc/idp5.bib holds the references
```

## Authors and license

Heiko Dietrich (Monash University) and Henrik Schanze (TU
Braunschweig). The package is distributed under the GNU General Public
License, version 2 or later; see the file `LICENSE`.
