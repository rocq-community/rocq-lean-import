From LeanImport Require Import Lean.
(* Large dump (Init.PropLemmas, decompressed from dumps/logic.ndjson.zip by the
   tests Makefile): exercise the NDJSON parser over the whole file without the
   (slow / partly pathological) translation. *)
Set Lean Just Parsing.
Redirect "ndjson_logic.log" Lean Import "../dumps/logic.ndjson".
