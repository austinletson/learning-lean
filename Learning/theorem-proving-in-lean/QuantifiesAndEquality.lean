variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  have axpq : (∀ x, p x ∧ q x) → (∀ x, p x) ∧ (∀ x, q x) :=
    fun h: (∀ x, p x ∧ q x) =>
      have hl : (∀ x, p x) :=
        fun y : α => show p y from (h y).left
      have hr : (∀ x, q x) :=
        fun y : α => show q y from (h y).right
      show (∀ x, p x) ∧ (∀ x, q x) from And.intro hl hr
  have axpaxq : (∀ x, p x) ∧ (∀ x, q x) → (∀ x, p x ∧ q x) :=
    fun h : (∀ x, p x) ∧ (∀ x, q x) =>
      show (∀ x, p x ∧ q x) from
        fun x : α => show p x ∧ q x
          from And.intro (h.left x) (h.right x)
  show  (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) from ⟨axpq, axpaxq⟩

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun hxp : (∀ x, p x → q x) =>
  fun hx : (∀ x, p x) =>
    fun x : α => (hxp x) (hx x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun hpx_qx : (∀ x, p x) ∨ (∀ x, q x) =>
    show ∀ x, p x ∨ q x from
      fun x : α => show p x ∨ q x
        from Or.elim hpx_qx
          (fun hp => Or.inl (hp x))
          (fun hq => Or.inr (hq x))


variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := sorry
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry
