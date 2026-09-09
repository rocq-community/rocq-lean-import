mutual
  inductive MutTree where
    | node : MutForest → MutTree

  inductive MutForest where
    | nil : MutForest
    | cons : MutTree → MutForest → MutForest
end

noncomputable def mutualFoldTree : MutTree → Nat :=
  MutTree.rec (fun _ result => result + 1) 0
    (fun _ _ treeResult forestResult => treeResult + forestResult)

mutual
  def MutTree.size : MutTree → Nat
    | .node forest => forest.size + 1

  def MutForest.size : MutForest → Nat
    | .nil => 0
    | .cons tree forest => tree.size + forest.size
end

noncomputable def mutualExample : Nat :=
  mutualFoldTree (.node (.cons (.node .nil) .nil))
