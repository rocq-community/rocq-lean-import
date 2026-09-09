universe u

inductive PartialRose (α : Type u) where
  | node : α → Array (PartialRose α) → PartialRose α

noncomputable def partialRoseSize {α : Type u} : PartialRose α → Nat :=
  PartialRose.rec
    (motive_1 := fun _ => Nat)
    (motive_2 := fun _ => Nat)
    (motive_3 := fun _ => Nat)
    (fun _ _ childrenSize => childrenSize + 1)
    (fun _ listSize => listSize)
    0
    (fun _ _ headSize tailSize => headSize + tailSize)

noncomputable def partialNestedExample : Nat :=
  partialRoseSize
    (PartialRose.node 1 (Array.mk [PartialRose.node 2 (Array.mk [])]))
