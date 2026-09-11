From LeanImport Require Import Lean.
(* Large dump: exercise the NDJSON parser over the whole file without the
   (slow / partly pathological) translation. *)
Set Lean Just Parsing.
Redirect "ndjson_core.log" Lean Import "../dumps/core.ndjson".
