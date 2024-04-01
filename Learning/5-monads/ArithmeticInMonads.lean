inductive Expr (op : Type) where
  | const : Int → Expr op
  | prim : op → Expr op → Expr op → Expr op


inductive Arith where
  | plus
  | minus
  | times
  | div

def evaluateM [Monad m] (apply : Arith -> Int -> Int -> m Int) : Expr Arith -> m Int
  | Expr.const i => pure i
  | Expr.prim op e1 e2 =>
    evaluateM apply e1 >>= fun v1 =>
    evaluateM apply e2 >>= fun v2 =>
    apply op v1 v2


-- Reader Monad

def Reader (ρ : Type) (α : Type) : Type := ρ -> α

def read : Reader ρ ρ := fun env => env

def Reader.pure (x : α) : Reader ρ α := fun _ => x

-- Reader ρ α -> (α -> Reader ρ β) -> Reader ρ β
-- (ρ -> α) -> (α -> (ρ -> β)) -> (ρ -> β)
def Reader.bind {ρ : Type} {α : Type} {β : Type}
 (result : ρ -> α) (next : α -> ρ -> β) : ρ -> β :=
 fun env => next (result env) env


abbrev Env : Type := List (String × (Int → Int → Int))

-- Exercises

-- Check monad contract for State σ

-- bind (pure v) f = f v
-- bind (fun sp => (sp, v)) f = f v
-- fun s => let (s', x) := ((fun sp => (sp, v)) s)  f x s' = f v
-- fun s => let (s', x) := (s, v) f x s' = f v
-- fun s => f v s = f v
-- f v = f v

-- bind v pure = v
-- fun s => let (s', x) := (v s) pure x s' = v
-- fun s => let (s', x) := (v s) (pure x) s' = v
-- fun s => let (s', x) := (v s) (fun sp => (sp, x)) s' = v
-- fun s => let (s', x) := (v s) (s' x) = v
-- fun s => v s = v
-- v = v -- because v is a function

-- bind (bind v f) g = bind v (fun x => bind (f x) g)
-- left side
--   bind (bind v f) g
--   bind (fun si => (s', xi) := (v si) f xi s') g
--
--   fun so =>
--     let (s'', xo) := (fun si => let (s', xi) := (v si) f xi s') so
--     g xo s''
--
--   fun so =>
--     let (s'', xo) := (let (s', xi) := (v so) f xi s')
--     g xo s''
--
--   fun so =>
--     let (s', xi) := (v so)
--     let (s'', xo) := (f xi s')
--     g xo s''
--   rename variables
--   fun s =>
--     let (s', x) := v s
--     let (s'', x') := f x s'
--     g x' s''
--

-- right side
--   bind v (fun x => bind (f x) g)
--   bind v (fun x => (fun si => let (s' xi) := ((f x) si) g xi s'))


--  fun so =>
--     let (s'', xo) = v so
--     (fun x => (fun si => let (s' xi) := ((f x) si) g xi s')) xo s''

--  fun so =>
--     let (s'', xo) = v so
--     (fun si => let (s' xi) := ((f xo) si) g xi s')) s''
--
--  fun so =>
--     let (s'', xo) = v so
--     let (s' xi) := ((f xo) s'')
--     g xi s'

--   rename variables
--  fun s =>
--     let (s', x) = v s
--     let (s'' x') := f x s'
--     g x' s''

-- left side = right side qed

-- Argument for Except ε is the same as Option


-- Readers with Failure

def ReaderOption (ρ : Type) (α : Type) : Type := ρ → Option α


def ReaderOption.pure (x : α) : ReaderOption ρ α := fun _ => some x

def ReaderOption.bind {ρ : Type} {α : Type} {β : Type}
  (r : ρ -> Option α) (next: α -> ρ -> Option β) : ρ -> Option β :=
  fun env =>
  r env >>= fun x =>
  next x env

instance : Monad (ReaderOption ρ) where
  pure := ReaderOption.pure
  bind := ReaderOption.bind

def applyPrimReaderOption (op: String) (x : Int) (y: Int) : ReaderOption Env Int :=
