#############################################################################
##
##  idp5.gd                                                 Idp5 package
##
##  Declarations of the public functions, and the text of the manual (built
##  with makedoc.g).  Everything else in the package is internal and lives in
##  the p5id_* namespace.
##
#############################################################################

#! @Chapter Introduction
#! @ChapterLabel intro

#! @Section Overview
#!   This package identifies the groups of order dividing <M>p^5</M>, for any
#!   prime <M>p</M>, with the groups in the SmallGroups library
#!   <Cite Key="BEO02"/>, and it constructs isomorphisms onto the library groups.
#!   The algorithms are described in <Cite Key="DES"/>.
#!   <P/>
#!   The SmallGroups library contains all groups of order <M>p^5</M>, but its
#!   identification function <Ref Attr="IdGroup" BookName="smallgrp"/> is not
#!   available for the groups of order <M>p^5</M> with <M>p \geq 7</M>.  After
#!   loading <Package>Idp5</Package>, <Ref Attr="IdSmallGroup" BookName="smallgrp"/>
#!   (equivalently <Ref Attr="IdGroup" BookName="smallgrp"/>) works for all
#!   groups of order <M>p^n</M> with <M>n \leq 5</M>; see
#!   Section <Ref Sect="Section_IdSmallGroup"/>.  Moreover, the package
#!   provides the attribute <Ref Attr="IsomorphismSmallGroup" Label="for IsGroup"/>, which
#!   constructs an isomorphism from a group <M>G</M> of order dividing
#!   <M>p^5</M> onto <C>SmallGroup(IdSmallGroup(G))</C>.
#!   <P/>
#!   The package adds its identification to the SmallGroups library, so
#!   after loading <Package>Idp5</Package>,
#!   <Ref Func="IdGroupsAvailable" BookName="smallgrp"/> returns <K>true</K>
#!   for the orders <M>p^5</M>, <M>p \geq 7</M>.
#!   <P/>
#!   The identification of a group of order dividing <M>p^4</M> also yields an
#!   isomorphism onto the library group.  The
#!   identification of a group of order <M>p^5</M> uses invariants, the
#!   identification of quotients of order dividing <M>p^4</M>, and linear algebra
#!   for the families of groups that depend on parameters.  An isomorphism
#!   from a group of order <M>p^5</M> onto the library group is then
#!   constructed by lifting isomorphisms between quotients, partly with a
#!   randomised search; see Section <Ref Sect="Section_IsomorphismSmallGroup"/>.
#!   <P/>
#!   The randomised lifting algorithm for the isomorphisms of groups of order
#!   <M>p^5</M> has been developed with the LLM Claude Opus; every isomorphism
#!   that it returns is verified.  The package files and this manual have
#!   been prepared with the assistance of Claude Opus.

#! @Section An example
#!   We identify a randomly generated permutation group isomorphic to
#!   <C>SmallGroup(7^5,65)</C>, and construct an isomorphism onto the
#!   library group.
#! @BeginExampleSession
#! gap> R := SmallGroup(7^5, 65);;
#! gap> R := Image(IsomorphismPermGroup(R));;
#! gap> repeat gens := List([1..8], x -> Random(R)); until Group(gens) = R;
#! gap> R := Group(gens);;
#! gap> IdSmallGroup(R);
#! [ 16807, 65 ]
#! gap> iso := IsomorphismSmallGroup(R);;
#! gap> Source(iso) = R;
#! true
#! gap> IdSmallGroup(Range(iso));
#! [ 16807, 65 ]
#! @EndExampleSession
#!   Each call of <C>SmallGroup(7^5,65)</C> creates a new group, so
#!   <C>Range(iso)</C> is not equal to a group <C>H</C> constructed with
#!   <C>H := SmallGroup(7^5,65)</C>.  However, both groups are given by the same
#!   pc presentation, so mapping <C>Pcgs(Range(iso))</C> onto <C>Pcgs(H)</C>
#!   defines an isomorphism.
#! @BeginExampleSession
#! gap> H := SmallGroup(7^5, 65);;
#! gap> isoRtoH := iso * GroupHomomorphismByImages(Range(iso), H,
#! >                                   Pcgs(Range(iso)), Pcgs(H));;
#! gap> Source(isoRtoH) = R and Range(isoRtoH) = H and IsBijective(isoRtoH);
#! true
#! @EndExampleSession


#! @Chapter Functions

#! @Section Identification
#! @SectionLabel IdSmallGroup
#!   The package registers the identification of the groups of order
#!   <M>p^5</M>, <M>p &gt; 5</M> prime, with the SmallGroups library.  For
#!   such a group <M>G</M>, the attribute
#!   <Ref Attr="IdSmallGroup" BookName="smallgrp"/> (a synonym of
#!   <Ref Attr="IdGroup" BookName="smallgrp"/>) then returns the pair
#!   <C>[p^5,i]</C> such that <M>G</M> is isomorphic to
#!   <C>SmallGroup(p^5,i)</C>, and
#!   <Ref Func="IdGroupsAvailable" BookName="smallgrp"/> returns <K>true</K>
#!   for <M>p^5</M>.  All other groups, in particular those of order
#!   <M>p^n</M> with <M>n \leq 4</M> and those of order <M>2^5</M>,
#!   <M>3^5</M> and <M>5^5</M>, are identified by the SmallGroups library
#!   itself.
#!   <P/>
#!   The input group can be given in any representation in which &GAP; can
#!   compute with it, for example as a pc group, a permutation group, or a
#!   matrix group.
#! @BeginExampleSession
#! gap> G := Group(GeneratorsOfGroup(SmallGroup(11^5, 40)));;
#! gap> IdGroup(G);
#! [ 161051, 40 ]
#! gap> G := Image(RegularActionHomomorphism(SmallGroup(7^5, 9)));;
#! gap> IdSmallGroup(G);
#! [ 16807, 9 ]
#! gap> IdGroupsAvailable(17^5);
#! true
#! gap> NumberSmallGroups(17^5);
#! 101
#! gap> ForAll([1..101], i -> IdGroup(Group(GeneratorsOfGroup(SmallGroup(17^5,i))))
#! >                          = [17^5, i]);
#! true
#! @EndExampleSession

#! @Section Isomorphisms onto the library groups
#! @SectionLabel IsomorphismSmallGroup

#! @Arguments G
#! @Returns an isomorphism from <A>G</A> onto
#!   <C>SmallGroup(IdSmallGroup(<A>G</A>))</C>, or <K>fail</K>
#! @Description
#!   For a group <A>G</A> of order <M>p^n</M> with <M>p</M> prime and
#!   <M>n \leq 5</M>, this attribute is an isomorphism from <A>G</A> onto the
#!   library group <C>SmallGroup(IdSmallGroup(<A>G</A>))</C>.
#!   <List>
#!   <Item>
#!     If <M>p &gt; 5</M> and <M>n \leq 4</M>, then the isomorphism is computed
#!     together with the ID by the identification algorithm of the package.
#!   </Item>
#!   <Item>
#!     If <M>p \in \{2,3\}</M>, or if <M>p=5</M> and <M>n \leq 4</M>, then
#!     &GAP;'s function <C>IsomorphismGroups</C> is used.
#!   </Item>
#!   <Item>
#!     If <M>n=5</M> and <M>p \geq 5</M>, then the isomorphism is constructed
#!     by lifting isomorphisms between quotients of <A>G</A> and of the
#!     library group, partly with a randomised search.  The map that is
#!     returned is always verified to be an isomorphism.  In principle the
#!     search can fail, and then <K>fail</K> is returned and a message is
#!     printed at level 1 of <Ref InfoClass="InfoIdp5"/>; this has not been
#!     observed in practice.  Since <Ref Attr="IsomorphismSmallGroup" Label="for IsGroup"/> is an
#!     attribute, the value <K>fail</K> is stored; to try again, call
#!     <Ref Attr="IsomorphismSmallGroup" Label="for IsGroup"/> for a new copy of the group, for
#!     example <C>Group(GeneratorsOfGroup(<A>G</A>))</C>.
#!   </Item>
#!   </List>
#!   Each call of <C>SmallGroup</C> creates a new group, so the range of the
#!   isomorphism is not equal to another group constructed with
#!   <C>SmallGroup(IdSmallGroup(<A>G</A>))</C>; but the two groups are given by
#!   the same pc presentation (see the example in Chapter <Ref Chap="Chapter_intro"/>).
DeclareAttribute( "IsomorphismSmallGroup", IsGroup );

#! @BeginExampleSession
#! gap> G := Image(IsomorphismPermGroup(SmallGroup(7^5, 30)));;
#! gap> iso := IsomorphismSmallGroup(G);;
#! gap> IsBijective(iso) and Source(iso) = G;
#! true
#! gap> IdSmallGroup(Range(iso));
#! [ 16807, 30 ]
#! gap> G := DirectProduct(CyclicGroup(IsPermGroup, 4), DihedralGroup(IsPermGroup, 8));;
#! gap> iso := IsomorphismSmallGroup(G);;
#! gap> IdSmallGroup(Range(iso)) = IdSmallGroup(G);
#! true
#! @EndExampleSession

#! @Section Types of the groups of order p^5
#! @SectionLabel Types
#!   For primes <M>p \geq 7</M>, the SmallGroups library constructs the groups
#!   of order <M>p^5</M> from 70 parametrised pc presentations; the number
#!   <M>t \in \{1, \ldots, 70\}</M> of the presentation of a group is its
#!   <E>type</E>.  The groups of a type form a consecutive range of IDs.  Most
#!   types consist of a single group; the types 11, 12, 29, 32, 33, 48 and 50
#!   have a further parameter <M>k</M>, and the pair <M>[t,k]</M> determines
#!   a group of type <M>t</M>.  The following two functions convert between
#!   the IDs and the types.

#! @Arguments p, i
#! @Returns a list <C>[t]</C> or <C>[t,k]</C>
#! @Description
#!   For a prime <A>p</A> <M>&gt; 5</M> and an integer <A>i</A> in
#!   <C>[1..NumberSmallGroups(<A>p</A>^5)]</C>, this function returns the
#!   type of <C>SmallGroup(<A>p</A>^5,<A>i</A>)</C>: the list <C>[t]</C> if
#!   the type <M>t</M> has no further parameter, and the list <C>[t,k]</C>
#!   otherwise.
DeclareGlobalFunction( "TypeFromIdSmallGroup_p5" );

#! @Arguments p, type
#! @Returns an integer or a list of integers
#! @Description
#!   This is the inverse of <Ref Func="TypeFromIdSmallGroup_p5"/>.  For a
#!   prime <A>p</A> <M>&gt; 5</M>, the argument <A>type</A> can be an integer
#!   <M>t</M> in <C>[1..70]</C> or a list <C>[t]</C>; then the IDs <M>i</M>
#!   of the groups <C>SmallGroup(<A>p</A>^5,i)</C> of type <M>t</M> are
#!   returned, as an integer if there is only one such group and as a list
#!   otherwise.  If <A>type</A> is a pair <C>[t,k]</C>, then the ID of the
#!   <M>k</M>-th group of type <M>t</M> is returned.
DeclareGlobalFunction( "IdSmallGroupFromType_p5" );

#! @BeginExampleSession
#! gap> TypeFromIdSmallGroup_p5(7, 34);
#! [ 29, 2 ]
#! gap> IdSmallGroupFromType_p5(7, [29, 2]);
#! 34
#! gap> IdSmallGroupFromType_p5(7, 29);
#! [ 33, 34, 35 ]
#! gap> TypeFromIdSmallGroup_p5(7, 65);
#! [ 52 ]
#! gap> IdSmallGroupFromType_p5(7, 52);
#! 65
#! gap> ForAll([1..NumberSmallGroups(7^5)],
#! >           i -> IdSmallGroupFromType_p5(7, TypeFromIdSmallGroup_p5(7, i)) = i);
#! true
#! @EndExampleSession

#! @Section The info class
#! @Description
#!   The info class of the package.  At level 1 (the default), a message is
#!   printed if the randomised search of <Ref Attr="IsomorphismSmallGroup" Label="for IsGroup"/>
#!   fails.  At levels 2 and 3, the construction of isomorphisms for groups of
#!   order <M>p^5</M> prints which of its cases has been used, and some
#!   statistics.
DeclareInfoClass( "InfoIdp5" );
SetInfoLevel( InfoIdp5, 1 );

#! @Section Testing the package
#! @SectionLabel Testing
#!   The test suite of the package is run with <C>TestPackage("idp5")</C>.  It
#!   identifies random copies of all groups of order <M>p^n</M>, <M>n \leq 5</M>,
#!   for several primes <M>p</M>, constructs isomorphisms onto the library
#!   groups, and runs the examples of this manual; this takes about a minute.
#!   The following function runs similar tests for given primes and prints
#!   runtimes.

#! @Arguments lps, nr, testIso
#! @Returns a record with the runtimes and the failures
#! @Description
#!   For every prime <M>p</M> in the list <A>lps</A>, every <M>e</M> in
#!   <C>[1..5]</C> and every <M>i</M> in <C>[1..NumberSmallGroups(p^e)]</C>,
#!   this function constructs <A>nr</A> random isomorphic copies of
#!   <C>SmallGroup(p^e,i)</C> (pc groups with respect to a random pcgs), and
#!   checks that <Ref Attr="IdSmallGroup" BookName="smallgrp"/> returns
#!   <C>[p^e,i]</C>.  If <A>testIso</A> is <K>true</K>, then it also checks
#!   that <Ref Attr="IsomorphismSmallGroup" Label="for IsGroup"/> returns an isomorphism onto the
#!   library group.  For each copy, the runtimes in milliseconds are printed.
#!   For the groups of order <M>p^5</M>, the average runtimes and the ten largest
#!   runtimes are printed at the end, as well as the numbers of wrong IDs, of
#!   failed isomorphism searches, and of returned maps that are not
#!   isomorphisms.  A wrong ID, and a map that is not an isomorphism, also cause
#!   an error.
#!   <P/>
#!   The returned record has the components <C>id</C> and <C>iso</C> (lists of
#!   triples <C>[time, p, i]</C> for the groups <C>SmallGroup(p^5,i)</C>),
#!   <C>wrong</C>, <C>failed</C> and <C>notiso</C> (lists of the groups for
#!   which the ID was wrong, the isomorphism search failed, or the returned map
#!   was not an isomorphism).  The runtimes depend on the machine.
DeclareGlobalFunction( "TestSmallGroupID_p5" );

#! @BeginLogSession
#! gap> t := TestSmallGroupID_p5([37, 61, 101], 1, true);;
#! ------ start p = 37
#! ID [37^1,1] copy 1:   id 2 ms,  iso 0 ms
#! ID [37^2,1] copy 1:   id 1 ms,  iso 0 ms
#! ID [37^2,2] copy 1:   id 1 ms,  iso 0 ms
#! ...
#! ID [101^5,267] copy 1:   id 1 ms,  iso 11 ms
#! ID [101^5,268] copy 1:   id 3 ms,  iso 31 ms
#! ID [101^5,269] copy 1:   id 1 ms,  iso 1 ms
#!
#! ------ summary
#! average time for ID: 51 ms   (607 tests)
#! ten largest runtimes for ID:
#!    273 ms   for SmallGroup(101^5,257)
#!    235 ms   for SmallGroup(101^5,256)
#!    ...
#! average time for iso: 71 ms   (607 tests)
#! ten largest runtimes for iso:
#!    3187 ms   for SmallGroup(101^5,125)
#!    1595 ms   for SmallGroup(101^5,119)
#!    ...
#! wrong IDs: 0
#! isomorphism search failed: 0
#! returned map not an isomorphism: 0
#! @EndLogSession
