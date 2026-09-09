structure PairPayload (α : Type) where
  left : α
  right : α

structure NestedPayload (α : Type) where
  values : List α
  value : α
