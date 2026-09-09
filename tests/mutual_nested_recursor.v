From LeanImport Require Import Lean.

Lean Import "../dumps/mutual_nested_recursor".

Check optionNestedExample : Nat.
Check mutualNestedExample : Nat.

Example optionNestedExample_computes : optionNestedExample = 3.
Proof. cbv. reflexivity. Qed.

Example mutualNestedExample_computes : mutualNestedExample = 4.
Proof. cbv. reflexivity. Qed.
