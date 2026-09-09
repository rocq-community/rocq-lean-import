From LeanImport Require Import Lean.

Set Lean Error Mode "Fail".

(* Stop after the container/Rose declarations, before roseSize at line 812. *)
Lean Import "../dumps/nested_containers" 1 812.
Check Rose.
