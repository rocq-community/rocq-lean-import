From LeanImport Require Import Lean.
(* Large dump (decompressed from dumps/init.ndjson.zip by the tests Makefile):
   parse the whole file without translating. *)
Set Lean Just Parsing.
Redirect "ndjson_init.log" Lean Import "../dumps/init.ndjson".
