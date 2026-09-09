From LeanImport Require Import Lean.
Set Lean Error Mode "Fail".
Lean Import "../dumps/constructor_owner".
Check repro : Token.
Fail Check (repro : Nat).
