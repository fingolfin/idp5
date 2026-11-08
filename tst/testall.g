#############################################################################
##
##  testall.g                                               Idp5 package
##
##  Runs all test files in tst/ (about a minute): tst/idp5.tst and the
##  examples of the manual in tst/idp501.tst (extracted by makedoc.g).
##
LoadPackage( "idp5" );
TestDirectory( DirectoriesPackageLibrary( "idp5", "tst" ),
  rec( exitGAP := true ) );
FORCE_QUIT_GAP( 1 ); # if we ever get here, there was an error
