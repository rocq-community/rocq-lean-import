inductive OptionTree where
  | leaf : OptionTree
  | branch : Option OptionTree → OptionTree

noncomputable def optionTreeSize (tree : OptionTree) : Nat :=
  OptionTree.rec
    (motive_1 := fun _ => Nat)
    (motive_2 := fun _ => Nat)
    1
    (fun _ nestedSize => nestedSize + 1)
    0
    (fun _ nestedSize => nestedSize)
    tree

noncomputable def optionTreeAuxSize (tree : Option OptionTree) : Nat :=
  OptionTree.rec_1
    (motive_1 := fun _ => Nat)
    (motive_2 := fun _ => Nat)
    1
    (fun _ nestedSize => nestedSize + 1)
    0
    (fun _ nestedSize => nestedSize)
    tree

noncomputable def optionNestedExample : Nat :=
  optionTreeSize (.branch (some .leaf))
    + optionTreeAuxSize (some (.branch none))

mutual
  inductive NestedTree where
    | node : List NestedForest → NestedTree

  inductive NestedForest where
    | empty : NestedForest
    | child : NestedTree → NestedForest
end

noncomputable def nestedTreeSize (tree : NestedTree) : Nat :=
  NestedTree.rec
    (motive_1 := fun _ => Nat)
    (motive_2 := fun _ => Nat)
    (motive_3 := fun _ => Nat)
    (fun _ nestedSize => nestedSize + 1)
    0
    (fun _ nestedSize => nestedSize)
    0
    (fun _ _ headSize tailSize => headSize + tailSize)
    tree

noncomputable def nestedForestSize (forest : NestedForest) : Nat :=
  NestedForest.rec
    (motive_1 := fun _ => Nat)
    (motive_2 := fun _ => Nat)
    (motive_3 := fun _ => Nat)
    (fun _ nestedSize => nestedSize + 1)
    0
    (fun _ nestedSize => nestedSize)
    0
    (fun _ _ headSize tailSize => headSize + tailSize)
    forest

noncomputable def nestedListSize (forest : List NestedForest) : Nat :=
  NestedTree.rec_1
    (motive_1 := fun _ => Nat)
    (motive_2 := fun _ => Nat)
    (motive_3 := fun _ => Nat)
    (fun _ nestedSize => nestedSize + 1)
    0
    (fun _ nestedSize => nestedSize)
    0
    (fun _ _ headSize tailSize => headSize + tailSize)
    forest

noncomputable def mutualNestedExample : Nat :=
  let inner := NestedTree.node []
  let outer := NestedTree.node [.empty, .child inner]
  nestedTreeSize outer + nestedForestSize (.child inner)
    + nestedListSize [.empty, .child inner]
