structure Payload (α : Type) where
  tag : Nat
  value : α

inductive RecordTree where
  | leaf : RecordTree
  | node : List (Payload RecordTree) → RecordTree

noncomputable def recordTreeSize (tree : RecordTree) : Nat :=
  RecordTree.rec
    (motive_1 := fun _ => Nat)
    (motive_2 := fun _ => Nat)
    (motive_3 := fun _ => Nat)
    1
    (fun _ nestedSize => nestedSize + 1)
    0
    (fun _ _ headSize tailSize => headSize + tailSize)
    (fun tag _ valueSize => tag + valueSize)
    tree

noncomputable def recordListSize
    (trees : List (Payload RecordTree)) : Nat :=
  RecordTree.rec_1
    (motive_1 := fun _ => Nat)
    (motive_2 := fun _ => Nat)
    (motive_3 := fun _ => Nat)
    1
    (fun _ nestedSize => nestedSize + 1)
    0
    (fun _ _ headSize tailSize => headSize + tailSize)
    (fun tag _ valueSize => tag + valueSize)
    trees

noncomputable def recordPayloadSize
    (payload : Payload RecordTree) : Nat :=
  RecordTree.rec_2
    (motive_1 := fun _ => Nat)
    (motive_2 := fun _ => Nat)
    (motive_3 := fun _ => Nat)
    1
    (fun _ nestedSize => nestedSize + 1)
    0
    (fun _ _ headSize tailSize => headSize + tailSize)
    (fun tag _ valueSize => tag + valueSize)
    payload

noncomputable def nestedRecordExample : Nat :=
  let payload : Payload RecordTree := { tag := 2, value := .leaf }
  recordTreeSize (.node [payload]) + recordListSize [payload]
    + recordPayloadSize payload
