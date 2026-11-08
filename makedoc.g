#############################################################################
##
##  makedoc.g                                               Idp5 package
##
##  Builds the manual in doc/ from the comments in gap/idp5.gd, and extracts
##  the examples of the manual into tst/idp501.tst:
##
##    gap makedoc.g
##
##  Only the files used by GAP's help system are kept: manual.six (index),
##  chap*.txt (text), chap*.html with manual.css and manual.js (browser),
##  manual.pdf, and manual.lab (references from other manuals), and the
##  source of the bibliography, idp5.bib.
##
if fail = LoadPackage("AutoDoc", ">= 2019.04.10") then
  Error("AutoDoc version 2019.04.10 or newer is required");
fi;

AutoDoc(rec(
  autodoc := true,
  scaffold := rec(MainPage := true, bib := "idp5.bib"),
  extract_examples := true,
));

# AutoDoc always produces an additional MathJax version of the HTML pages.
# Build the manual once more without it.  Newer versions of AutoDoc call the
# main file _main.xml, older ones Idp5.xml.
main := First(["_main", "Idp5"],
              f -> IsExistingFile(Concatenation("doc/", f, ".xml")));
MakeGAPDocDoc("doc", main, [], "Idp5");
GAPDocManualLabFromSixFile("Idp5", "doc/manual.six");

# Remove the intermediate files.
for file in DirectoryContents("doc") do
  if ForAny([".aux", ".bbl", ".blg", ".brf", ".idx", ".ilg", ".ind", ".log", ".out",
             ".pnr", ".tex", ".toc", ".xml", "_mj.html"],
            ext -> EndsWith(file, ext))
     or file in ["chooser.html", "lefttoc.css", "nocolorprompt.css",
                 "ragged.css", "rainbow.js", "times.css", "toggless.css",
                 "toggless.js"] then
    RemoveFile(Filename(Directory("doc"), file));
  fi;
od;
QUIT;
