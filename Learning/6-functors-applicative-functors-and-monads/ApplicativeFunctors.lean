inductive Validate (ε α : Type) : Type where
  | ok : α → Validate ε α
  | errors : List ε → Validate ε α

structure CheckedInput (thisYear : Nat) : Type where
  name : {n : String // n ≠ ""}
  birthYear : {y : Nat // y > 1900 ∧ y ≤ thisYear}

instance : Functor (Validate ε) where
  map f validate :=
    match validate with
      | .ok x => .ok $ f x
      | .errors es => .errors es

instance : Applicative (Validate ε) where
  pure x := .ok x
  seq f x :=
    match f with
      | .ok g => g <$> x ()
      | .errors es =>
        match x () with
          | .ok _ => .errors es
          | .errors e => .errors (es ++ e)
