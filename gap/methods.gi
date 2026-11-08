#############################################################################
##
##  methods.gi                                              Idp5 package
##
##  The methods for IdSmallGroup and IsomorphismSmallGroup.
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
## method for groups of order p^i with i<=5 and p>5
##
InstallMethod( IdSmallGroup,
    "for groups of order p^i with i <= 5 and p > 5, via p5id_IdSmallGroup",
    [ IsGroup ],
    SUM_FLAGS,   # rank this above the SmallGrp library methods
function( G )
    local n, f;
    if not IsFinite( G ) then
        TryNextMethod();
    fi;
    n := Size( G );
    if n = 1 then SetIdGroup(G,[1,1]); return [1,1]; fi;
    f := Collected(FactorsInt(n));
    if not Size(f)=1 or not f[1][2] <= 5 or not f[1][1]>5 then
        TryNextMethod();
    fi;
    return p5id_IdSmallGroup( G );
end );
