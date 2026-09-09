universe u

structure Box (α : Sort u) where
  value : α

def boxedTrue : Box True := ⟨True.intro⟩

def nonemptyTrue : Nonempty True := ⟨True.intro⟩
