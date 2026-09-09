From LeanImport Require Import Lean.

Lean Import "../dumps/nested_partial_application".

Check partialRoseSize : forall A : Type, PartialRose A -> Nat.

Example partialNestedExample_computes : partialNestedExample = 2.
Proof. cbv. reflexivity. Qed.
