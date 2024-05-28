structure RawInput where
  name : String
  birthYear : String

def Field := String deriving Repr, ToString

def f : Field := "test"
