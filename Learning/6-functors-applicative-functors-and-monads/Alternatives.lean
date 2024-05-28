import Learning.«6-functors-applicative-functors-and-monads».ApplicativeFunctors
import Learning.«6-functors-applicative-functors-and-monads».LegacyValidation

-- instance  :  Functor (Validate ε) where
--   map f
--    | .ok x => .ok (f x)
--    | .errors errs => .errors errs

-- instance [Append ε] : Applicative (Validate ε) where
--   pure := .ok
--   seq f x :=
--     match f with
--     | .ok g => g <$> (x ())
--     | .errors errs =>
--       match x () with
--       | .ok _ => .errors errs
--       | .errors errs' => .errors (errs ++ errs')


-- def Validate.orElse [Append ε] (a : Validate ε α) (b : Unit → Validate ε α) : Validate ε α :=
--   match a with
--   | .ok x => .ok x
--   | .errors errs1 =>
--     match b () with
--     | .ok x => .ok x
--     | .errors errs2 => .errors (errs1 ++ errs2)

-- instance [Append ε] : OrElse (Validate ε α) where
--   orElse := Validate.orElse


-- def Validate.mapErrors : Validate ε α → (ε → ε') → Validate ε' α
--   | .ok a, _ => .ok a
--   | .errors errs, f => .errors (f errs)




-- inductive TreeError where
--   | field : Field → String → TreeError
--   | path : String → TreeError → TreeError
--   | both : TreeError → TreeError → TreeError
-- deriving Repr

-- instance : Append TreeError where
--   append := .both

-- def report : TreeError → String
--   | .field f msg => let fieldString : String := f; s!"field: {fieldString} error with msg: {msg}"
--   | .path path tree => s!"path: {path} \n  {report tree}"
--   | .both tree1 tree2 => s!"{report tree1}\n{report tree2}"

-- instance : ToString TreeError where
--   toString := report



-- def reportError (f : Field) (msg : String) : Validate TreeError α :=
--   .errors (.field f msg)


def Validate.orElse (a : Validate ε α) (b : Unit → Validate ε α) : Validate ε α :=
  match a with
  | .ok x => .ok x
  | .errors errs1 =>
    match b () with
    | .ok x => .ok x
    | .errors errs2 => .errors (errs1 ++ errs2)

instance : OrElse (Validate ε α) where
  orElse := Validate.orElse



def checkThat (condition : Bool) (field : Field) (msg : String) : Validate (Field × String) Unit :=
  if condition then pure () else reportError field msg


def checkCompany (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  -- first checks that the birth year is valid and then throws the result away
  checkThat (input.birthYear == "FIRM") "birth year" "FIRM if a company" *>
  -- builds a validated company with the company name
  .company <$> checkName input.name

def checkSubtype {α : Type} (v : α) (p : α → Prop) [Decidable (p v)] (err : ε) : Validate ε {x : α // p x} :=
  if h : p v then
    pure ⟨v, h⟩
  else
    .errors { head := err, tail := [] }

def checkHumanBefore1970 (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanBefore1970 <$>
      checkSubtype y (fun x => x > 999 ∧ x < 1970) ("birth year", "less than 1970") <*>
      pure input.name

def checkHumanAfter1970 (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanAfter1970 <$>
      checkSubtype y (· > 1970) ("birth year", "greater than 1970") <*>
      checkName input.name

def checkLegacyInput (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  checkCompany input <|> checkHumanBefore1970 input <|> checkHumanAfter1970 input


#eval checkLegacyInput ⟨"Johnny's Troll Groomers", "FIRM"⟩

#eval checkLegacyInput ⟨"", "1970"⟩
