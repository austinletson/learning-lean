import Std.Data.Rat

inductive MyExcept (ε : Type) (α : Type) where
  | error : ε -> MyExcept ε α
  | ok : α -> MyExcept ε α
deriving BEq, Hashable, Repr

instance : Monad (MyExcept ε) where
  pure x := MyExcept.ok x
  bind except f :=
    match except with
      | MyExcept.ok x  => f x
      | MyExcept.error e => MyExcept.error e

def State (σ : Type) (α : Type) : Type :=
  σ -> (σ × α)

def get : State σ σ :=
  fun s => (s, s)

def set (s : σ) : State σ Unit :=
  fun _ => (s, ())

instance : Monad (State σ) where
  pure x := fun s => (s, x)
  -- State σ α -> (α -> State σ β) -> State σ β
  -- (σ -> (σ × α)) -> (α -> (σ -> (σ × β))) -> (σ -> (σ × β))
  bind state next := fun s =>
    let (s', x) := state s
    next x s'

structure WithLog (σ : Type) (α : Type) :=
  log : List σ
  val : α
deriving Repr

def write (l : σ) : WithLog σ Unit :=
  {log := [l], val := ()}

def isEven (i : Int) : Bool :=
  i % 2 == 0
instance : Monad (WithLog σ) where
  pure x := {log := [], val := x}
  -- (WithLog σ α) -> (α -> (WithLog σ β) -> (WithLog σ β))
  bind wl next :=
    let {log := l, val := x} := wl
    let {log := l', val := x'} := next x
    {log := l ++ l', val := x' }

def saveIfEven (i : Int) : WithLog Int Int :=
  (if isEven i then
    write i
   else pure ()) >>= fun () =>
  pure i

def mapM [Monad m] (f : α → m β) : List α -> m (List β)
  | [] => pure []
  | x::xs =>
    f x >>= fun px =>
    mapM f xs >>= fun pxs =>
    pure (px::pxs)
-- bind : m α -> (α -> m β) -> m β
-- bind : m β -> (β -> m (List β)) -> m (List β)


def nums := [1, 0, 3, 3]
def intNums := List.map Int.ofNat nums


def reciprocal : Nat -> MyExcept String Rat
  | 0 => MyExcept.error "Cannot divide by zero"
  | n => MyExcept.ok (Rat.divInt 1 n)


#eval mapM saveIfEven intNums


inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α
deriving Repr

def BinTree.mapM [Monad m] (f : α -> m β) : BinTree α -> m (BinTree β)
  | BinTree.leaf => pure BinTree.leaf
  | BinTree.branch l x r =>
      mapM f l >>= fun pl =>
      f x >>= fun px =>
      mapM f r >>= fun pr =>
      pure (BinTree.branch pl px pr)

open BinTree in
def aTree :=
  branch
    (branch
       (branch leaf (1 : Int) (branch leaf (2 : Int) leaf))
       (3 :Int)
       leaf)
    (4 : Int)
    (branch leaf (5: Int) leaf)

#eval BinTree.mapM saveIfEven aTree


inductive MyOption (α : Type) : Type where
  | none : MyOption α
  | some : α -> MyOption α

instance : Monad MyOption where
  pure x := MyOption.some x
  bind op next := match op with
    | MyOption.none => MyOption.none
    | MyOption.some x => next x

-- bind (pure v) f = f v
-- bind (MyOption.some v) f = f v
-- f v = f v

-- bind v pure = v
-- by cases:
-- bind MyOption.none pure = MyOption.none
-- bind (MyOption.some v) pure = pure v = MyOption.some v

-- bind (bind v f) = bind v (fun x => bind (f x ) g)
-- by cases:
-- bind (bind (Option.some v) f) g = bind (Option.some v) ( fun x => bind (f x) g)
-- bind (f v) g = bind (f v ) g

instance : Monad Option where
  pure x := some x
  bind opt next := none

-- why does this violate the monad contract?
-- it violates all the laws, for example pure is not a left identity of bind

-- bind (pure v) f = f v
-- bind (MyOption.some v) f = f v
-- none = f v
