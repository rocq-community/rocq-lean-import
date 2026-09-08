From LeanImport Require Import Lean.

Lean Import "../dumps/universe_instances".

Universe a b.
Constraint Set < a.
Constraint a < b.

(* The Lean parameters occur only inside successor/maximum expressions, so
   the translated declaration has exactly the two universes used by its type. *)
Check UniverseBox@{a b} : Type@{a} -> Type@{b}.
Check universeValueType : UniverseBox_inst1 Nat.
