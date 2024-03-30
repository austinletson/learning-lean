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

-- Exercises

-- Check monad contract for State σ

-- bind (pure v) f = f v
-- bind (fun sp => (sp, v)) f = f v
-- fun s => let (s', x) := ((fun sp => (sp, v)) s)  f x s' = f v
-- fun s => let (s', x) := (s, v) f x s' = f v
-- fun s => f v s = f v
-- f v = f v

-- WIP
-- bind v pure = v
-- bind v (fun sp => (sp, xp)) = v
-- fun s => let (s', x) := (v s) ((fun sp => (sp, xp)) x) s' = v
-- fun s => let (s', x) := (v s) (x, xp)
