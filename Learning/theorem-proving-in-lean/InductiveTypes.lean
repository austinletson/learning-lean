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

namespace Hidden
inductive List (α : Type u) where
| nil  : List α
| cons : α → List α → List α
namespace List
def append (as bs : List α) : List α :=
 match as with
 | nil       => bs
 | cons a as => cons a (append as bs)
theorem nil_append (as : List α) : append nil as = as :=
 rfl
theorem cons_append (a : α) (as bs : List α)
                    : append (cons a as) bs = cons a (append as bs) :=
 rfl

theorem append_nil (as : List α) : append as nil = as :=
  List.recOn
    (motive := fun as => append as nil = as) as
    (show append nil nil = nil from rfl)
    (fun (a : α) (as : List α) (ih : append as nil = as) =>
      show append (cons a as) nil = cons a as from
      calc append (cons a as) nil
        _ = cons a (append as nil) := by rw [cons_append]
        _ = cons a as := by rw [ih]
    )

theorem append_nil_tact (as : List α) : append as nil = as :=
  List.recOn
    (motive := fun as => append as nil = as) as rfl
    (fun a as ih => by simp [cons_append, ih])



theorem append_assoc (as bs cs : List α)
        : append (append as bs) cs = append as (append bs cs) :=
  List.recOn
    (motive := fun k => append (append k bs) cs = append k (append bs cs)) as
    (by simp [nil_append])
    (fun (a : α) (as : List α) (ih : append (append as bs) cs = append as (append bs cs)) =>
      show append (append (cons a as) bs) cs = append (cons a as) (append bs cs) from
      calc append (append (cons a as) bs) cs
        _ = cons a (append (append as bs) cs) := by repeat (rw [cons_append])
        _ = cons a (append as (append bs cs)) := by rw [ih]
        _ = append (cons a as) (append bs cs) := by rw [← cons_append])

theorem append_assoc_tact (as bs cs : List α)
        : append (append as bs) cs = append as (append bs cs) :=
  List.recOn
    (motive := fun k => append (append k bs) cs = append k (append bs cs)) as
    (by simp [nil_append])
    (fun a as ih => by simp [cons_append, ih])

end List
end Hidden
