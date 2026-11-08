#############################################################################
##
##  types.gi                                                Idp5 package
##
##  Conversion between the IDs of the groups of order p^5, p > 5, in the
##  SmallGroups library and their types in the construction of these groups
##  in the library.
##
#############################################################################

#######################################################################
## Returns id(s) of groups of order p^5 that that belong to type. If more than one
## group belongs to type, a list of ids is returned. If just one groups has type,
## the id itself is returned.
## input: prime p and type (either a single integer, or a list [t] or [t,k])
## output: a single interger or a list of integers
##
InstallGlobalFunction( IdSmallGroupFromType_p5, function(p, type)
    local res, gettypes, ids;

    if not IsPrimeInt(p) or not p>5 or
       not ((IsInt(type) and type in [1..70]) or
            (IsList(type) and Length(type)=1 and type[1] in [1..70]) or
            (IsList(type) and Length(type)=2 and type[1] in [1..70]
                          and IsPosInt(type[2]))) then
       Error("wrong input");
    fi;
    ## a type [t] as returned by TypeFromIdSmallGroup_p5
    if IsList(type) and Length(type)=1 then type := type[1]; fi;

    gettypes := function(p,i)
        local f, c, w,a,b,type,k;
        w := IntFFE( Z( p ) );
        a := Gcd( p - 1, 3 );
        b := Gcd( p - 1, 4 );
        if i <= 10 then
            type := i;
        elif i <= 11 + (p - 1) / 2 - 1 then
            type := 11;
            k := i - 10;
        elif i <= 11 + p - 2 then
            type := 12;
            k := i - (11 + (p - 1) / 2 - 1);
        elif i <= 25 + p then
            type := i - p + 3;
        elif i <= 25 + p + a then
            type := 29;
            k := i - (25 + p);
        elif i <= 27 + p + a then
            type := i - p - a + 4;
        elif i <= 27 + p + 2 * a then
            type := 32;
            k := i - (27 + p + a);
        elif i <= 27 + p + 2 * a + b then
            type := 33;
            k := i - (27 + p + 2 * a);
        elif i <= 41 + p + 2 * a + b then
            type := i - p - 2 * a - b + 6;
        elif i <= 41 + p + 2 * a + b + (p - 1) / 2 then
            type := 48;
            k := i - (41 + p + 2 * a + b);
        elif i = 42 + p + 2 * a + b + (p - 1) / 2 then
            type := 49;
        elif i <= 42 + p + 2 * a + b + p - 1 then
            type := 50;
            k := i - (42 + p + 2 * a + b + (p - 1) / 2);
        else
            type := i - 2 * p - 2 * a - b + 9;
        fi;
        return type;
    end;

    if IsInt(type) then
        ids := Filtered([1..NumberSmallGroups(p^5)],i->gettypes(p,i)=type);
        if Size(ids) = 1 then ids := ids[1]; fi;
    elif IsList(type) then
        ids := Filtered([1..NumberSmallGroups(p^5)],i->gettypes(p,i)=type[1]);
        if Size(ids) < type[2] then Error("Type does not exist"); fi;
        ids := ids[type[2]];
    fi;

    return ids;
end );



#######################################################################
## the inverse of IdSmallGroupFromType_p5
## input: prime p>5 and i in [1..NumberSmallGroups(p^5)]
## output: the type of the group with IDSmallGroup=[p^5,i]
##
InstallGlobalFunction( TypeFromIdSmallGroup_p5, function(p,i)
local f, c, w,a,b,typ,k;

    if not IsPrimeInt(p) or not p>5 or not i in [1..NumberSmallGroups(p^5)] then
       Error("wrong input");
    fi;
    f := FreeGroup( 5 );
    c := CombinatorialCollector( f, [ p, p, p, p, p ] );
    w := IntFFE( Z( p ) );
    a := Gcd( p - 1, 3 );
    b := Gcd( p - 1, 4 );
    k := false;

    if i <= 10 then
        typ := i;
    elif i <= 11 + (p - 1) / 2 - 1 then
        typ := 11;
        k := i - 10;
    elif i <= 11 + p - 2 then
        typ := 12;
        k := i - (11 + (p - 1) / 2 - 1);
    elif i <= 25 + p then
        typ := i - p + 3;
    elif i <= 25 + p + a then
        typ := 29;
        k := i - (25 + p);
    elif i <= 27 + p + a then
        typ := i - p - a + 4;
    elif i <= 27 + p + 2 * a then
        typ := 32;
        k := i - (27 + p + a);
    elif i <= 27 + p + 2 * a + b then
        typ := 33;
        k := i - (27 + p + 2 * a);
    elif i <= 41 + p + 2 * a + b then
        typ := i - p - 2 * a - b + 6;
    elif i <= 41 + p + 2 * a + b + (p - 1) / 2 then
        typ := 48;
        k := i - (41 + p + 2 * a + b);
    elif i = 42 + p + 2 * a + b + (p - 1) / 2 then
        typ := 49;
    elif i <= 42 + p + 2 * a + b + p - 1 then
        typ := 50;
        k := i - (42 + p + 2 * a + b + (p - 1) / 2);
    else
        typ := i - 2 * p - 2 * a - b + 9;
    fi;

    if IsInt(k) then
        return [typ, k];
    else
        return [typ];
    fi;
end );
