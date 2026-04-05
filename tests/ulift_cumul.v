From LeanImport Require Import Lean.

(* Test: ULift imported with cumulativity uses definitions instead of an inductive *)
Set Lean ULift To Cumulativity.
Redirect "ulift_cumul.log" Lean Import "../dumps/ulift".

(* Verify ULift_cumul is convertible with the identity type function:
   α should be accepted where ULift_cumul α is expected *)
Check (fun (α : Type) (x : α) => (x : ULift_cumul α)).

(* Verify the round trip: ULift_down_cumul (ULift_up_cumul x) = x *)
Check (fun (α : Type) (x : α) => ULift_down_cumul (ULift_up_cumul x) : α).

(* Verify that the imported ULift_down is well-typed *)
Check ULift_down.