universe u
class Inhabited' (α : Sort u) where
  default : α

axiom MyProp : Prop
axiom mp : MyProp

def h : Inhabited' MyProp := Inhabited'.mk mp
def test : MyProp := h.default

theorem Inhabited'.eta α (x : Inhabited' α) : Inhabited'.mk x.default = x := by rfl
axiom h2 : Inhabited' MyProp
def test_eta := Inhabited'.eta MyProp h2
