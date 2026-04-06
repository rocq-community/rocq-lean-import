From LeanImport Require Import Lean.

(* Test: Without cumulative ULift registrations, ULift is translated as an
   inductive. The type of example1 uses the inductive ULift, so the bare
   convertibility check (without the inductive wrapper) should fail. *)
Redirect "ulift_no_cumul.log" Lean Import "../dumps/ulift".

(* example1 has type Scratch_MyProd (ULift Scratch_MyNat) Type *)
Check Scratch_example1.

(* Without cumulativity, ULift is an inductive, so it is NOT convertible
   with the bare type. This check must fail. *)
Fail Check Scratch_example1 : Scratch_MyProd Scratch_MyNat Type.
