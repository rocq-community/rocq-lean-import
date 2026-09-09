From LeanImport Require Import Lean.

Lean Import "../dumps/nested_containers".

Check roseSize : forall A : Type, Rose A -> Nat.
Check nestedExample : Nat.
Check nestedAuxExample : Nat.
Check nestedProdExample : Nat.

Example nestedExample_computes : nestedExample = 2.
Proof. cbv. reflexivity. Qed.

Example nestedAuxExample_computes : nestedAuxExample = 2.
Proof. cbv. reflexivity. Qed.

Example nestedProdExample_computes : nestedProdExample = 3.
Proof. cbv. reflexivity. Qed.
