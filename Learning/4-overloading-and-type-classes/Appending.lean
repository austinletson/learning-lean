import Learning.«4-overloading-and-type-classes».ArraysAndIndexing

instance : Append (NonEmptyList α) where
  append xs ys :=
    { head := xs.head, tail := xs.tail ++ ys.head :: ys.tail }
