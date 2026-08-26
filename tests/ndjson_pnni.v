From LeanImport Require Import Lean.
(* Large dump (Init.Data.Nat.Basic, decompressed from dumps/pnni.ndjson.zip by
   the tests Makefile): exercise the NDJSON parser over the whole file without
   the (slow / partly pathological) translation. *)
Set Lean Just Parsing.
Redirect "ndjson_pnni.log" Lean Import "../dumps/pnni.ndjson".
