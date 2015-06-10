(*i camlp4deps: "parsing/grammar.cma" i*)

open Hextraction

VERNAC COMMAND EXTEND HExtraction CLASSIFIED AS QUERY
| [ "Hextraction" ne_global_list(x) ] -> [ extraction x ]
| [ "Hextraction" "Module" ne_global_list(x) ] -> [ module_extraction x ]
END

