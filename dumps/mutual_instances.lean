universe u

mutual
  inductive PolyTree (α : Sort u) : Type u where
    | node : α → PolyForest α → PolyTree α

  inductive PolyForest (α : Sort u) : Type u where
    | nil : PolyForest α
    | cons : PolyTree α → PolyForest α → PolyForest α
end

def polyPropExample : PolyTree True :=
  .node True.intro (.cons (.node True.intro .nil) .nil)

mutual
  inductive MutualP : Prop where
    | intro : MutualQ → MutualP

  inductive MutualQ : Prop where
    | intro : MutualP → MutualQ
end
