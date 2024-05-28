import Learning.«6-functors-applicative-functors-and-monads».LegacyValidation
import Learning.«6-functors-applicative-functors-and-monads».Input

inductive Validate' (ε α : Type) : Type where
  | ok : α → Validate' ε α
  | errors : ε → Validate' ε α
deriving Repr

instance : Functor (Validate' ε) where
  map f validate :=
    match validate with
      | .ok x => .ok $ f x
      | .errors es => .errors es

instance [Append ε]: Applicative (Validate' ε) where
  pure x := .ok x
  seq f x :=
    match f with
      | .ok g => g <$> x ()
      | .errors es =>
        match x () with
          | .ok _ => .errors es
          | .errors e => .errors (es ++ e)

def Validate'.orElse [Append ε] (a : Validate' ε α) (b : Unit → Validate' ε α) : Validate' ε α :=
  match a with
  | .ok x => .ok x
  | .errors es1 =>
    match b () with
    | .ok x => .ok x
    | .errors es2 => .errors (es1 ++ es2)

instance [Append ε] : OrElse (Validate' ε α) where
  orElse := Validate'.orElse


def Validate'.mapErrors : Validate' ε α → (ε → ε') → Validate' ε' α
  | .ok x , _ => .ok x
  | .errors es, f => .errors (f es)

inductive TreeError where
  | field : Field → String → TreeError
  | path : String → TreeError → TreeError
  | both : TreeError → TreeError → TreeError
deriving Repr

instance : Append TreeError where
  append := .both


def reportError (f : Field) (msg : String) : Validate' TreeError α :=
  .errors (.field f msg)

def reportPath (path: String) (v : Validate' TreeError α) : Validate' TreeError α :=
  match v with
    | .ok x => .ok x
    | .errors tree => .errors (.path path tree)

def checkName (name : String) : Validate' TreeError {n : String // n ≠ ""} :=
  reportPath "checkName" $
  if h : name = "" then
    reportError "name" "Required"
  else pure ⟨name, h⟩

def Validate'.andThen (val : Validate' ε α) (next : α → Validate' ε β) : Validate' ε β :=
  match val with
  | .errors errs => .errors errs
  | .ok x => next x

def checkYearIsNat (year : String) : Validate' TreeError Nat :=
  reportPath "checkYearIsNat" $
  match year.trim.toNat? with
  | none => reportError "birth year" "Must be digits"
  | some n => pure n

def checkThat (condition : Bool) (field : Field) (msg : String) : Validate' TreeError Unit :=
  if condition then pure () else reportError field msg

def checkCompany (input : RawInput) : Validate' TreeError LegacyCheckedInput :=
  reportPath "checkCompany" $
  -- first checks that the birth year is valid and then throws the result away
  checkThat (input.birthYear == "FIRM") "birth year" "FIRM if a company" *>
  -- builds a validated company with the company name
  .company <$> checkName input.name

def checkSubtype {α : Type} (v : α) (p : α → Prop) [Decidable (p v)] (err : ε) : Validate' ε {x : α // p x} :=
  if h : p v then
    .ok ⟨v, h⟩
  else
    .errors err

def checkHumanBefore1970 (input : RawInput) : Validate' TreeError LegacyCheckedInput :=
  reportPath "checkHumanBefore1970" $
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanBefore1970 <$>
      checkSubtype y (fun x => x > 999 ∧ x < 1970) (.field "birth year" "less than 1970") <*>
      pure input.name

def checkHumanAfter1970 (input : RawInput) : Validate' TreeError LegacyCheckedInput :=
  reportPath "checkHumanAfter1970" $
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanAfter1970 <$>
      checkSubtype y (· > 1970) (.field "birth year" "greater than 1970") <*>
      checkName input.name

def checkLegacyInput (input : RawInput) : Validate' TreeError LegacyCheckedInput :=
  checkCompany input <|> checkHumanBefore1970 input <|> checkHumanAfter1970 input

#eval checkLegacyInput ⟨"Johnny's Troll Groomers", "FIRM"⟩

def report : TreeError → String
  | .field field msg => s!"Error validating {field}: {msg}\n"
  | .path msg tree => s!"{msg} -> " ++ (report tree)
  | .both tree1 tree2 => (report tree1) ++ (report tree2)

def printErrors (v : Validate' TreeError α) : IO Unit := do
  match v with
    | .ok _ => println! "No errors"
    | .errors tree => println! (report tree)

#eval checkLegacyInput ⟨"", "1970"⟩
#eval printErrors (checkLegacyInput ⟨"", "FIRM"⟩)
