import Learning.«5-monads».TheMonadTypeClass

def OptionT' (m : Type u → Type v) (α : Type u) : Type v :=
  m (Option α)

def OptionT'.mk (x : m (Option α)) : OptionT m α := x

def OptionT'.run (x : OptionT m α) : m (Option α) := x



instance [Monad m] : Monad (OptionT' m) where
  pure x := OptionT'.mk (pure (some x))
  bind action next := OptionT'.mk do
    match ← action with
    | none => pure none
    | some v => next v

structure WithLogT (σ : Type u) (m: Type u → Type v)  (α : Type u): Type v :=
  log : m (List σ)
  val : m α


instance [Monad m] : Monad (WithLogT σ m) where
  pure x := {log := pure [], val := pure x}
  bind action next :=
    let {log := ml, val := mx} := action
    let {log := l', val := x'}  := do next (← mx)
    {log := l ++ l', val := ( ← x')}
