inductive list.{u} (α : Sort u)
  | nil  : list α
  | cons : α → list α → list α
inductive RecInd.{u} (A : Sort u)
  | mk : A → list (RecInd A) → RecInd A

-- Definitional eta does NOT hold for RecInd
-- Propositional eta
theorem RecInd.eta (x : RecInd A) : RecInd.mk x.1 x.2 = x := by
  fail_if_success rfl
  cases x; rfl
