namespace Hidden
inductive Bool where
  | false : Bool
  | true  : Bool

def and (a b : Bool) : Bool :=
  match a with
  | Bool.true => b
  | Bool.false => Bool.false

def or (a b : Bool) : Bool :=
  match a with
  | Bool.true => Bool.true
  | Bool.false => b

def not (a : Bool) : Bool :=
  match a with
  | Bool.true => Bool.false
  | Bool.false => Bool.true

theorem de_morgan_law (a b : Bool) : not (and a b) = (or (not a) (not b)) :=
  match a with
  | Bool.true =>
    match b with
    | Bool.true => rfl
    | Bool.false => rfl
  | Bool.false =>
    match b with
    | Bool.true => rfl
    | Bool.false => rfl

end Hidden

def partialComp {α β : Type} (f : α → Option β) (g : β → Option γ) : α → (Option γ) :=
  fun a => match f a with
    | some b => g b
    | none => none

def fun1 (b : Bool) : Option Nat :=
  match b with
  | true => some 1
  | false => none

def fun2 (n : Nat) : Option Bool :=
  match n with
  | 1 => some true
  | _ => none

def fun1_then_fun2 : Bool → Option Bool := partialComp fun1 fun2

#eval fun1_then_fun2 true



namespace Hidden
inductive Option (α : Type u) where
  | none : Option α
  | some : α → Option α

inductive Inhabited (α : Type u) where
  | mk : α → Inhabited α

def inhabitedBool : Inhabited Bool := Inhabited.mk Bool.true
def inhabitedNat : Inhabited Nat := Inhabited.mk 1

theorem prod_inhabited_inhabited {α β : Type} (ia : Inhabited α) (ib : Inhabited β) : (Inhabited (α × β)) :=
  let (Inhabited.mk a) := ia
  let (Inhabited.mk b) := ib
  Inhabited.mk (a, b)

theorem fun_to_inhabited_inhabited {α β : Type} (ib : Inhabited β) : (Inhabited (α → β)) :=
  let (Inhabited.mk b) := ib
  Inhabited.mk (fun _ => b)


end Hidden
