universe u

inductive Rose (α : Type u) where
  | node : α → Array (Rose α) → Rose α

noncomputable def roseSize {α : Type u} (tree : Rose α) : Nat :=
  Rose.rec
    (motive_1 := fun _ => Nat)
    (motive_2 := fun _ => Nat)
    (motive_3 := fun _ => Nat)
    (fun _ _ childrenSize => childrenSize + 1)
    (fun _ listSize => listSize)
    0
    (fun _ _ headSize tailSize => headSize + tailSize)
    tree

noncomputable def nestedExample : Nat :=
  roseSize (Rose.node 1 (Array.mk [Rose.node 2 (Array.mk [])]))

noncomputable def roseArraySize {α : Type u}
    (trees : Array (Rose α)) : Nat :=
  Rose.rec_1
    (motive_1 := fun _ => Nat)
    (motive_2 := fun _ => Nat)
    (motive_3 := fun _ => Nat)
    (fun _ _ childrenSize => childrenSize + 1)
    (fun _ listSize => listSize)
    0
    (fun _ _ headSize tailSize => headSize + tailSize)
    trees

noncomputable def roseListSize {α : Type u}
    (trees : List (Rose α)) : Nat :=
  Rose.rec_2
    (motive_1 := fun _ => Nat)
    (motive_2 := fun _ => Nat)
    (motive_3 := fun _ => Nat)
    (fun _ _ childrenSize => childrenSize + 1)
    (fun _ listSize => listSize)
    0
    (fun _ _ headSize tailSize => headSize + tailSize)
    trees

noncomputable def nestedAuxExample : Nat :=
  roseArraySize (Array.mk [Rose.node 1 (Array.mk [])])
    + roseListSize [Rose.node 2 (Array.mk [])]

inductive LabeledTree where
  | node : Array (Nat × LabeledTree) → LabeledTree

noncomputable def labeledSize (tree : LabeledTree) : Nat :=
  LabeledTree.rec
    (motive_1 := fun _ => Nat)
    (motive_2 := fun _ => Nat)
    (motive_3 := fun _ => Nat)
    (motive_4 := fun _ => Nat)
    (fun _ childrenSize => childrenSize + 1)
    (fun _ listSize => listSize)
    0
    (fun _ _ headSize tailSize => headSize + tailSize)
    (fun _ _ childSize => childSize)
    tree

noncomputable def labeledPairSize (pair : Nat × LabeledTree) : Nat :=
  LabeledTree.rec_3
    (motive_1 := fun _ => Nat)
    (motive_2 := fun _ => Nat)
    (motive_3 := fun _ => Nat)
    (motive_4 := fun _ => Nat)
    (fun _ childrenSize => childrenSize + 1)
    (fun _ listSize => listSize)
    0
    (fun _ _ headSize tailSize => headSize + tailSize)
    (fun _ _ childSize => childSize)
    pair

noncomputable def nestedProdExample : Nat :=
  let leaf := LabeledTree.node (Array.mk [])
  labeledSize (LabeledTree.node (Array.mk [(7, leaf)]))
    + labeledPairSize (7, leaf)
