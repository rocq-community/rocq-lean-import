From LeanImport Require Import Lean.
(* Large dump (Init.WF, which carries the Quot primitives; decompressed from
   dumps/quot.ndjson.zip by the tests Makefile): exercise the NDJSON parser over
   the whole file without the (slow / partly pathological) translation. *)
Set Lean Just Parsing.
Redirect "ndjson_quot.log" Lean Import "../dumps/quot.ndjson".
