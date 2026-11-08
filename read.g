#############################################################################
##
##  read.g                                                  Idp5 package
##
##  The files are read in this order so that every function is defined
##  before it is referred to.
##
ReadPackage( "idp5", "gap/types.gi" );    # IDs <-> types of the groups of order p^5
ReadPackage( "idp5", "gap/isop4.gi" );    # groups of order dividing p^4
ReadPackage( "idp5", "gap/idp5.gi" );     # identification of the groups of order p^5
ReadPackage( "idp5", "gap/isop5.gi" );    # isomorphisms for the groups of order p^5
ReadPackage( "idp5", "gap/methods.gi" );  # methods for IdSmallGroup, IsomorphismSmallGroup
ReadPackage( "idp5", "gap/testing.gi" );  # TestSmallGroupID_p5
