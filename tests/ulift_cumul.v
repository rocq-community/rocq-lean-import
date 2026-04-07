From LeanImport Require Import Lean ULiftCumulativeRegistration.

(* Import the example. ULift at instance 2 (s=SProp) is still an inductive
   since we only registered cumul definitions for instance 0. *)
Redirect "ulift_cumul.log" Lean Import "../dumps/ulift".

(* example1 still type-checks (instance 2 falls through to inductive) *)
Check Scratch_example1.

(* With cumulativity registered for instance 0, ULift_cumul is transparent,
   so α is convertible with ULift_cumul α. *)
Check (fun (α : Type) (x : α) => (x : ULift_cumul α)).
