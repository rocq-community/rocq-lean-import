From LeanImport Require Import Lean.

(* Regression: a recursive single-constructor inductive must NOT be
   declared as a primitive record, since the kernel rejects primitive
   records that don't admit eta. *)

Redirect "rec_single_ctor.log" Lean Import "../dumps/rec_single_ctor".

Definition root {A} (r : RecInd A) : A :=
  match r with RecInd_mk _ v _ => v end.

Definition is_singleton {A} (r : RecInd A) : bool :=
  match r with
  | RecInd_mk _ _ (list_nil _) => true
  | RecInd_mk _ _ (list_cons _ _ _) => false
  end.

(* Imported propositional eta from Lean. *)
Check RecInd_eta.

(* Propositional eta proved directly in Rocq via destruct. *)
Lemma RecInd_eta' {A} (x : RecInd A) :
  match x with RecInd_mk _ v cs => RecInd_mk A v cs end = x.
Proof. destruct x; reflexivity. Qed.
