#check 2 < 4

-- <$> is  infix for Functor.map

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α
deriving Repr

def idahoSpiders : NonEmptyList String := {
  head := "Banded Garden Spider",
  tail := [
    "Long-legged Sac Spider",
    "Wolf Spider",
    "Hobo Spider",
    "Cat-faced Spider"
  ]
}

def otherSpiders : List String := ["Other Spider"]
def noSpiders : List String := []


instance : Append (NonEmptyList α) where
  append xs ys :=
    { head := xs.head, tail := xs.tail ++ ys.head :: ys.tail }

def myhappend : (List α) -> (NonEmptyList α) -> (NonEmptyList α)
  | [], ys => ys
  | x :: xs, ys => { head := x, tail :=  xs ++ ys.head :: ys.tail }

instance : HAppend (List α) (NonEmptyList α) (NonEmptyList α) where
  hAppend := myhappend


#eval otherSpiders ++ idahoSpiders
#eval noSpiders ++ idahoSpiders

inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α


def fmap : (α -> β) -> (BinTree α) -> (BinTree β)
  | _,  BinTree.leaf => BinTree.leaf
  | f, BinTree.branch l x r => BinTree.branch (fmap f l) (f x) (fmap f r)

instance : Functor BinTree where
  map := fmap
