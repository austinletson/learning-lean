variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  have axpq : (∀ x, p x ∧ q x) → (∀ x, p x) ∧ (∀ x, q x) :=
    fun h: (∀ x, p x ∧ q x) =>
      have hl : (∀ x, p x) :=
        fun y : α => show p y from (h y).left
      have hr : (∀ x, q x) :=
        fun y : α => show q y from (h y).right
      show (∀ x, p x) ∧ (∀ x, q x) from And.intro hl hr
  have axpaxq : (∀ x, p x) ∧ (∀ x, q x) → (∀ x, p x ∧ q x):= _
  show  (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) from ⟨axpq, axpaxq⟩

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry
