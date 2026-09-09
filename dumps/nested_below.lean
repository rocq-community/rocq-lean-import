inductive NestedArrayProdBelow (α : Type) where
  | node : α → Array (Nat × NestedArrayProdBelow α) → NestedArrayProdBelow α

#check NestedArrayProdBelow.brecOn
