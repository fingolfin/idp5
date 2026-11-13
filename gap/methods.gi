#############################################################################
##
##  methods.gi                                              Idp5 package
##
##  The SmallGrp layer for IdSmallGroup, and the method for
##  IsomorphismSmallGroup.
##
#############################################################################

####################################################################################
##
## input: p-group of order dividing p^5
## output: IdSmallGroup
## If an isomorphism onto the library group is found on the way (this is the case
## for the groups of order dividing p^4), then it is stored as IsomorphismSmallGroup.
##
BindGlobal( "p5id_IdSmallGroup", function(G)
local id;
   if HasIdGroup(G) then return IdSmallGroup(G); fi;
   id := p5id_Idp5Group(G);
   if not id.iso = fail then SetIsomorphismSmallGroup(G, id.iso); fi;
   return id.id;
end );


####################################################################################
##
## input: p-group G of order dividing p^5
## output: isomorphism to SmallGroup(IdSmallGroup(G))
## N.B.: for groups of order p^5 the current algorithm is randomised and might fail;
##       in this case, "fail" is returned
##
BindGlobal( "p5id_IsomorphismSmallGroup", function(G)
local isopc, GG, id, iso, f;
   if Size(G)=1 then return IsomorphismGroups(G,SmallGroup(1,1)); fi;
   f := Collected(FactorsInt(Size(G)));
   if not Size(f)=1 or not f[1][2] <= 5 then Error("wrong input"); fi;
   f := f[1];
   if not IsPcGroup(G) then
      isopc := IsomorphismPcGroup(G);
      GG := Image(isopc);
   else
      isopc := IdentityMapping(G);
      GG := G;
   fi;
   if HasIdGroup(G) then SetIdGroup(GG,IdSmallGroup(G)); fi;
   id := p5id_IdSmallGroup(GG);
   if f[2]<5 or f[1] in [2,3]  then
      id := p5id_Idp5Group(GG);
      if not id.iso = fail then
         return isopc*id.iso;
      fi;
   fi;
   iso := p5id_iso_random_bruteforce(GG);
   if not iso=fail then
      return isopc*iso;
   fi;
   Info(InfoIdp5, 1, "IsomorphismSmallGroup: the randomised search failed; ",
        "call IsomorphismSmallGroup for a new copy of the group to try again");
   return fail;
end );


####################################################################################
##
## method for groups of order p^i with i<=5
##
InstallMethod( IsomorphismSmallGroup,
    "for groups of order p^i with i <= 5, via p5id_IsomorphismSmallGroup",
    [ IsGroup ],
    SUM_FLAGS,
function( G )
    local n, f;
    if not IsFinite( G ) then
        TryNextMethod();
    fi;
    n := Size( G );
    if n = 1 then return IsomorphismGroups(G,SmallGroup(1,1)); fi;
    f := Collected(FactorsInt(n));
    if not Size(f)=1 or not f[1][2] <= 5  then
        TryNextMethod();
    fi;
    return p5id_IsomorphismSmallGroup( G );
end );


####################################################################################
##
## SmallGrp layer for the identification of the groups of order p^5, p > 5.
## SmallGrp identifies the groups of order p^n, n <= 4, for every p, and those
## of order 2^5, 3^5, 5^5; its layers are consulted first, so claiming more
## orders here would have no effect.
##
BindGlobal( "p5id_IdAvailable", function( size )
local p;
   p := RootInt( size, 5 );
   if p^5 <> size or p <= 5 or not IsPrimeInt( p ) then return fail; fi;
   return rec( p := p );
end );

# an isomorphism found on the way is stored as IsomorphismSmallGroup of G;
# SmallGrp hands over the user's group if it is a pc or a permutation group
# of small degree, otherwise an isomorphic pc group
BindGlobal( "p5id_IdGroupInLayer", function( G, idrec )
   return p5id_IdSmallGroup( G )[2];
end );

if IsBound( SmallGroupsAddLayer ) then

# SmallGrp 1.7 and up
SmallGroupsAddLayer( rec(
    name := "Idp5",
    available := ReturnFail,  # the groups themselves come from SmallGrp
    group := ReturnFail,
    idAvailable := p5id_IdAvailable,
    id := p5id_IdGroupInLayer ) );

else

# SmallGrp before 1.7: claim a library slot and a function slot by hand,
# after those of the packages loaded so far
BindGlobal( "p5id_LAYER",
    Maximum( Length( SMALL_AVAILABLE_FUNCS ), Length( ID_AVAILABLE_FUNCS ) ) + 1 );
BindGlobal( "p5id_POS", Maximum( List( [
        SMALL_GROUP_FUNCS,
        SMALL_GROUPS_INFORMATION,
        NUMBER_SMALL_GROUPS_FUNCS,
        ID_GROUP_FUNCS,
        SELECT_SMALL_GROUPS_FUNCS,
    ], Length ) ) + 1 );

# binding the slot keeps the next package from taking it
SMALL_AVAILABLE_FUNCS[ p5id_LAYER ] := ReturnFail;

ID_AVAILABLE_FUNCS[ p5id_LAYER ] := function( size )
local r;
   r := p5id_IdAvailable( size );
   if r = fail then return fail; fi;
   r.lib := p5id_LAYER;
   r.func := p5id_POS;
   return r;
end;

ID_GROUP_FUNCS[ p5id_POS ] := p5id_IdGroupInLayer;

fi;
