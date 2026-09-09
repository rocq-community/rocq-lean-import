From LeanImport Require Import Lean.

Lean Import "../dumps/sprop_record_scheme".

Check Box_inst1 : SProp -> Type.
Check boxedTrue : Box_inst1 True.
Check Nonempty_inst1 : SProp -> SProp.
Check nonemptyTrue : Nonempty_inst1 True.
