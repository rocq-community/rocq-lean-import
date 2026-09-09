From LeanImport Require Import Lean.

Lean Import "../dumps/nested_record_eligibility".

Check PairPayload : Type -> Type.
Fail Check PairPayload_all.

Check NestedPayload : Type -> Type.
Fail Check NestedPayload_all.
