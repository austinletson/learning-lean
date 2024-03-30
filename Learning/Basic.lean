import Init.System.FilePath
import Init.System.Platform




#check (@IO.println)

#eval Bool.true

def testParentAcrossOS (p : System.FilePath) (windowsParent : Option String) (unixParent : Option String) : Bool :=
  if System.Platform.isWindows then
    p.parent == windowsParent
  else
    p.parent == unixParent

#eval testParentAcrossOS "c:/a/b" "c:/a" "c:/a"
#eval testParentAcrossOS "c:/a" "c:/" "c:"
#eval testParentAcrossOS "c:/" none "c:"
#eval testParentAcrossOS "c:" none none


structure Pos where
  succ ::
  pred : Nat

instance : Add Pos where
  add n k := Pos.succ $ (n.pred + 1) + (k.pred + 1) - 1

instance : ToString Pos where
  toString n := toString $ n.pred + 1

instance : Mul Pos where
  mul n k := Pos.succ $ (n.pred + 1) * (k.pred + 1) - 1

instance : OfNat Pos (n + 1) where
  ofNat := Pos.succ n

def one : Pos := 1

#eval (Pos.succ 1) * (Pos.succ 3)

#check @OfNat.ofNat
#check (@OfNat.ofNat Pos)


structure Even where
  twice::
  half : Nat

instance : ToString Even where
  toString n := toString $ n.half * 2

instance : Add Even where
  add n k := Even.twice $ ((n.half * 2) + (k.half * 2)) / 2

instance: Mul Even where
  mul n k := Even.twice $ ((n.half * 2) * (k.half * 2)) / 2

#eval (Even.twice 2) * (Even.twice 4)

#eval (Even.twice 0)

#check (@Add.add)



instance : OfNat Even Nat.zero where
  ofNat := Even.twice 0

instance [OfNat Even n] : OfNat Even (n + 2) where
  ofNat := Even.twice ((n + 2) / 2)



#check (@OfNat.ofNat Even Nat.zero)


def zero : Even := 0

def four : Even := 8

def recLimit : Even := 2

#eval four

structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

instance [Mul α] : HMul (PPoint α) α (PPoint α) where
  hMul p s  := {x := p.x * s, y := p.y * s}

#eval {x := 2.5, y := 3.7 : PPoint Float} * 2.0
