inductive Branch (α : Type) where
  | leaf
  | node : α → Branch α → Branch α → Branch α

structure Raw (α : Type) where
  inner : Branch α

structure Wrapped (α : Type) where
  inner : Raw α

inductive JsonLike where
  | arr : Array JsonLike → JsonLike
  | obj : Wrapped JsonLike → JsonLike

#check JsonLike.casesOn
#check JsonLike.brecOn
