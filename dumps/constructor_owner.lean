prelude

universe u

inductive Token : Type where
  | mk

structure Box (α : Type u) : Type u where
  value : α

def repro : Token := (Box.mk Token.mk).value
