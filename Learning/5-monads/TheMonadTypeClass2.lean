inductive MyExcept (ε : Type) (α : Type) where
  | error : ε → MyExcept ε α
  | ok : α → MyExcept ε α
deriving BEq, Hashable, Repr

instance : Monad (MyExcept ε) where
  pure x := MyExcept.ok x
  bind except f :=
    match except with
      | MyExcept.error e => MyExcept.error e
      | MyExcept.ok a => f a

def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs =>
    f x >>= fun hd =>
    mapM f xs >>= fun tl =>
    pure (hd :: tl)

def evens := [0,2,4,4]

def divByTwoOrError (n: Nat) : MyExcept String Nat :=
  if n % 2 == 0 then MyExcept.ok (n / 2) else MyExcept.error "n is odd"

#eval mapM divByTwoOrError evens


inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α
deriving Repr

def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)

#check State String

def get : State σ σ :=
  fun s => (s, s)

def set (s : σ) : State σ Unit :=
  fun _ => (s, ())

instance : Monad (State σ) where
  pure x := fun s => (s, x)
  -- State α → (α → State β) → State β
  bind state f :=
    fun s =>
      let (state', x) := state s
      f x state'



def increment (howMuch : Nat) : State Nat Nat :=
  get >>= fun x =>
  set (x + howMuch) >>= fun () =>
  pure x

#eval mapM increment evens 0








open BinTree in
def aTree :=
  branch
    (branch
       (branch leaf 1 (branch leaf 2 leaf))
       3
       leaf)
    4
    (branch leaf 0 leaf)

def sum (howMuch : Nat) : State Nat Nat :=
  get >>= fun i =>
  set (i + howMuch) >>= fun () =>
  pure i


def BinTree.mapM [Monad m] (f : α → m β) : BinTree α → m (BinTree β)
  | BinTree.leaf => pure BinTree.leaf
  | BinTree.branch r x l =>
    BinTree.mapM f r >>= fun r' =>
    f x >>= fun x' =>
    BinTree.mapM f l >>= fun l' =>
    pure $ BinTree.branch r' x' l'

#eval aTree

#eval BinTree.mapM sum aTree 0
