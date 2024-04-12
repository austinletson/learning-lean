structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α
deriving Repr

#eval 1 + 1
def trees : Array String := #["sloe", "birch"]

#eval trees[1]
