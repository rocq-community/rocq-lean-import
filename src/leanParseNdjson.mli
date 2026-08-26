open LeanExpr

type parsing_state

val empty_state : parsing_state
val is_ndjson_line : string -> bool
val do_prefix_line : lcnt:int -> parsing_state -> string -> parsing_state
val do_line : lcnt:int -> parsing_state -> string -> parsing_state * action option
val pp_state : parsing_state -> Pp.t
