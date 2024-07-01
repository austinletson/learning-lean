
def something? : Option String := none




def opLet : IO Unit := do
  let some x :=
    match something? with
      | some x => some x
      | none => none
    | IO.eprintln "error"

  println! x


def someExceptOk : Except String String := Except.ok "hello"
def someExceptError : Except String String := Except.error "error"

def ioCatch (eVal: Except String String) : IO (String) := do
  match eVal with
    | Except.ok val => return val
    | Except.error msg => IO.eprintln s!"error {msg}" *> return ""


def opExcept : IO Unit := do
  let Except.ok x := someExceptOk
    | IO.eprintln "error"
  println! x

  let y ← ioCatch someExceptError



  println! y


#eval opExcept
