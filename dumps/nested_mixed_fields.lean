inductive MixedFields (α : Type) where
  | node : Array α → Array (Nat × MixedFields α) → MixedFields α

#check MixedFields.casesOn
