(*i camlp4deps: "parsing/grammar.cma" i*)

open Hextraction

VERNAC COMMAND EXTEND Hextraction CLASSIFIED AS QUERY
| [ "Hextraction" ne_global_list(x) ] -> [ extraction x ]
END
