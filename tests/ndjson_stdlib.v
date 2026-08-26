From LeanImport Require Import Lean.
(* Large dump (decompressed from dumps/stdlib.ndjson.zip by the tests Makefile):
   parse the whole file without translating. *)
Set Lean Just Parsing.
Redirect "ndjson_stdlib.log" Lean Import "../dumps/stdlib.ndjson".
