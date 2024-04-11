inductive Validate (ε α : Type) : Type where
  | ok : α → Validate ε α
  | errors : ε → Validate ε α
deriving Repr

instance  :  Functor (Validate ε) where
  map f
   | .ok x => .ok (f x)
   | .errors errs => .errors errs

instance [Append ε] : Applicative (Validate ε) where
  pure := .ok
  seq f x :=
    match f with
    | .ok g => g <$> (x ())
    | .errors errs =>
      match x () with
      | .ok _ => .errors errs
      | .errors errs' => .errors (errs ++ errs')


def Validate.andThen (val : Validate ε α) (next : α → Validate ε β) : Validate ε β :=
  match val with
  | .errors errs => .errors errs
  | .ok x => next x

def Validate.orElse [Append ε] (a : Validate ε α) (b : Unit → Validate ε α) : Validate ε α :=
  match a with
  | .ok x => .ok x
  | .errors errs1 =>
    match b () with
    | .ok x => .ok x
    | .errors errs2 => .errors (errs1 ++ errs2)

instance [Append ε] : OrElse (Validate ε α) where
  orElse := Validate.orElse


def Validate.mapErrors : Validate ε α → (ε → ε') → Validate ε' α
  | .ok a, _ => .ok a
  | .errors errs, f => .errors (f errs)



def Field := String

inductive TreeError where
  | field : Field → String → TreeError
  | path : String → TreeError → TreeError
  | both : TreeError → TreeError → TreeError

instance : Append TreeError where
  append := .both

def report : TreeError → String
  | .field f msg => let fieldString : String := f; s!"field: {fieldString} error with msg: {msg}"
  | .path path tree => s!"path: {path} \n  {report tree}"
  | .both tree1 tree2 => s!"{report tree1}\n{report tree2}"

instance : ToString TreeError where
  toString := report


def reportError (f : Field) (msg : String) : Validate TreeError α :=
  .errors (.field f msg)


abbrev NonEmptyString := {s : String // s ≠ ""}

structure RawInput where
  name : String
  birthYear : String

inductive LegacyCheckedInput where
  | humanBefore1970 :
    (birthYear : {y : Nat // y > 999 ∧ y < 1970}) →
    String →
    LegacyCheckedInput
  | humanAfter1970 :
    (birthYear : {y : Nat // y > 1970}) →
    NonEmptyString →
    LegacyCheckedInput
  | company :
    NonEmptyString →
    LegacyCheckedInput
deriving Repr



def checkSubtype {α : Type} (v : α) (p : α → Prop) [Decidable (p v)] (err : ε) : Validate ε {x : α // p x} :=
  if h : p v then
    .ok ⟨v, h⟩
  else
    .errors err

def checkThat (condition : Bool) (field : Field) (msg : String) : Validate TreeError Unit :=
  if condition then pure () else reportError field msg

def checkName (name : String) : Validate TreeError {n : String // n ≠ ""} :=
  if h : name = "" then
    reportError "name" "Required"
  else pure ⟨name, h⟩

def checkYearIsNat (year : String) : Validate TreeError Nat :=
  match year.trim.toNat? with
  | none => reportError "birth year" "Must be digits"
  | some n => pure n


def checkCompany (input : RawInput) : Validate TreeError LegacyCheckedInput :=
  checkThat (input.birthYear == "FIRM") "birth year" "FIRM if a company" *>
  .company <$> checkName input.name

def checkHumanBefore1970 (input : RawInput) : Validate TreeError LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanBefore1970 <$>
      checkSubtype y (fun x => x > 999 ∧ x < 1970) (.field "birth year" "less than 70") <*>
      pure input.name

def checkHumanAfter1970 (input : RawInput) : Validate TreeError LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanAfter1970 <$>
      checkSubtype y (· > 1970) (.field "birth year" "greater than 1970") <*>
      checkName input.name

def checkLegacyInput (input : RawInput) : Validate TreeError LegacyCheckedInput :=
  checkCompany input <|> checkHumanBefore1970 input <|> checkHumanAfter1970 input



#eval checkLegacyInput ⟨"Johnny's Troll Groomers", "FIRM"⟩
