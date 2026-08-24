universe u v

axiom UniverseBox (α : Type u) : Type (max (u + 1) v)
axiom universeValue (α : Type u) : UniverseBox.{u, v} α

noncomputable def universeValueType : UniverseBox.{0, 1} Nat := universeValue Nat
