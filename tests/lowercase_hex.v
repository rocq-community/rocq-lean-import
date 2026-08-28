From LeanImport Require Import Lean.

(* lean4export emits uppercase bytes, but the format is hexadecimal rather
   than specifically uppercase hexadecimal. *)
Redirect "lowercase_hex.log" Lean Import "../dumps/lowercase_hex".

Fail Lean Import "../dumps/invalid_hex".
Fail Lean Import "../dumps/invalid_hex_width".
