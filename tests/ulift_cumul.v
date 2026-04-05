From LeanImport Require Import Lean.

(* Test: ULift imported with cumulativity uses definitions instead of an inductive.
   The cumulative definitions are registered in Lean.v, so the import automatically
   uses cumulativity for ULift. *)
Redirect "ulift_cumul.log" Lean Import "../dumps/ulift".

(* Verify that the imported Scratch_example1 has the correct type.
   With cumulativity, ULift is transparent, so ULift_cumul_inst2 Scratch_MyNat
   is convertible with Scratch_MyNat. *)
Check Scratch_example1 : Scratch_MyProd (ULift_cumul_inst2 Scratch_MyNat) Type.
Check Scratch_example1 : Scratch_MyProd Scratch_MyNat Type.
