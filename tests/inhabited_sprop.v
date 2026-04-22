From LeanImport Require Import Lean.

(* Regression for #63: Lean's Inhabited instantiated at Prop (mapped to
   SProp) must still support projection and dependent elimination. *)

Redirect "inhabited_sprop.log" Lean Import "../dumps/inhabited_sprop".

Check test.
Check test_eta.

Definition get_default {A} (x : Inhabited' A) : A :=
  match x with Inhabited'_mk _ v => v end.

Lemma inhabited_eta {A} (x : Inhabited' A) :
  Inhabited'_mk A (get_default x) = x.
Proof. destruct x; reflexivity. Qed.
