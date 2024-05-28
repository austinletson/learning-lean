variable {p : Prop}
variable {q : Prop}
theorem t1 : p → q → p := fun hp : p => fun hq : q => hp

#print t1
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  have hpq : p ∧ q → q ∧ p := (fun h : p ∧ q => ⟨h.right, h.left⟩)
  have hqp : q ∧ p → p ∧ q := (fun h : q ∧ p => ⟨h.right, h.left⟩)
  show p ∧ q ↔ q ∧ p from ⟨hpq, hqp⟩


example : p ∨ q ↔ q ∨ p :=
  have hpq : p ∨ q → q ∨ p := fun h =>
    Or.elim h
    (fun hp => Or.intro_right q hp)
    (fun hq => Or.intro_left p hq)
  have hqp : q ∨ p → p ∨ q := fun h =>
    Or.elim h
    (fun hq => Or.intro_right p hq)
    (fun hp => Or.intro_left q hp)
  show p ∨ q ↔ q ∨ p from ⟨hpq, hqp⟩

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  have hpqr : (p ∧ q) ∧ r → p ∧ (p ∧ r) := fun h =>
    have hq : q :
  have hpqr' : p ∧ (q ∧ r) → (p ∧ q) ∧ r := _
  ⟨hpqr, hpqr'⟩

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry
