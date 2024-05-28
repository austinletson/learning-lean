inductive Vect (α : Type u) : Nat → Type u where
  | nil : Vect α 0
  | cons : α → Vect α n → Vect α (n + 1)
deriving Repr


def ABC : Vect String 3 := .cons "A" (.cons "B" (.cons "C" .nil))

def DEF : Vect String 3 := .cons "D" (.cons "E" (.cons "F" .nil))

-- def Vect.append : Vect α n → Vect α m → Vect α (n + m)
--   | .nil, v => v
--   |.cons x xs, v => .cons x (append xs v)


def Vect.replicate (n : Nat) (x : α) : Vect α n := match n with
  | 0 => .nil
  | n + 1 => .cons x (replicate (n) x)

#eval Vect.replicate 3 "a"


def Vect.zip : Vect α n → Vect β n → Vect (α × β) n
  | .nil, .nil => .nil
  | .cons x xs, .cons y ys => .cons (x, y) (zip xs ys)

def Vect.map : (α → β) → Vect α n → Vect β n
  | f, .nil => .nil
  | f, .cons x xs => .cons (f x) (map f xs)

def Vect.unzip : Vect (α × β) n → Vect α n × Vect β n
  | .nil => (.nil, .nil)
  | .cons x xs =>
    let rest := unzip xs
    ((Vect.cons x.fst (rest.fst)), (Vect.cons x.snd (rest.snd)))

def Vect.snoc : Vect α n → α → Vect α (n + 1)
  | .nil, y => .cons y (.nil)
  | .cons x xs, y => .cons x (snoc xs y)

def Vect.reverse : Vect α n → Vect α n
  | .nil => .nil
  | .cons x cs => (reverse cs).snoc x

def Vect.drop : (n : Nat) → Vect α (k + n) → Vect α k
  | 0, v => v
  | n + 1, .cons _ xs => drop (n) xs

def Vect.take : (n : Nat) → Vect α (k + n) → Vect α n
  | 0, _ => .nil
  | n + 1, .cons x xs => .cons x (take n xs)

#eval ABC.reverse

#eval ABC.drop 2

#eval ABC.take 2


#eval (Vect.zip ABC DEF).unzip

#eval Vect.map String.decapitalize ABC
