From LeanImport Require Import Lean.
From Test Require Import nested_reload_prefix.

Set Lean Error Mode "Fail".

(* A fresh process must recover the container and recursor-family metadata,
   not only the declarations and parser nodes from the preceding module. *)
Lean Import "../dumps/nested_containers" 812.

Example nested_main_after_reload : nestedExample = 2.
Proof. cbv. reflexivity. Qed.

Example nested_aux_after_reload : nestedAuxExample = 2.
Proof. cbv. reflexivity. Qed.
