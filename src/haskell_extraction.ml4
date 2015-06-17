(*i camlp4deps: "parsing/grammar.cma" i*)

open Hextraction

VERNAC COMMAND EXTEND HExtraction CLASSIFIED AS QUERY
| [ "Hextraction" "Simple" ne_global_list(x) ] -> [ extraction [] x ]
| [ "Hextraction" "Module" ne_global_list(x) ] -> [ extraction x [] ]
| [ "Hextraction" global_list(x) "," global_list(y) ] -> [ extraction x y ]
END

