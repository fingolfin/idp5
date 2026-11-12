#############################################################################
##
##  makedoc.g                                               Idp5 package
##
##  Builds the manual in doc/ from the comments in gap/idp5.gd, and extracts
##  the examples of the manual into tst/idp501.tst and tst/idp502.tst:
##
##    gap makedoc.g
##
if fail = LoadPackage("AutoDoc", ">= 2019.04.10") then
  Error("AutoDoc version 2019.04.10 or newer is required");
fi;

AutoDoc(rec(
  autodoc := true,
  scaffold := rec(MainPage := true, bib := "idp5.bib"),
  extract_examples := true,
));
QUIT;
