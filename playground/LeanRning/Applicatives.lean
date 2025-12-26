structure RawInput where
  name : String
  birthYear : String

structure CheckedInput (thisYear : Nat) : Type where
  name : {n : String // n ≠ ""}
  birthYear : {y : Nat // y > 1900 ∧ y ≤ thisYear}
  deriving Repr

def validPerson : CheckedInput 2025 :=
  { name := ⟨"Alice", by decide⟩
    birthYear := ⟨1990, by decide⟩ }

def tryValidPerson (name : String) (year : Nat) : Option (CheckedInput 2025) :=
  if h : name ≠ "" ∧ year > 1900 ∧ year ≤ 2025 then
    some { name := ⟨name, by simp [h]⟩, birthYear := ⟨year, by simp [h]⟩ }
  else
    none

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α
  deriving Repr

def NonEmptyList.append (xs ys : NonEmptyList α) : NonEmptyList α :=
  ⟨xs.head, xs.tail ++ [ys.head] ++ ys.tail⟩

instance : Append (NonEmptyList α) where
  append xs ys :=
    { head := xs.head, tail := xs.tail ++ ys.head :: ys.tail }

instance : HAppend (NonEmptyList α) (List α) (NonEmptyList α) where
  hAppend xs ys :=
    { head := xs.head, tail := xs.tail ++ ys }

inductive Validate (ε α : Type) : Type where
  | ok : α → Validate ε α
  | errors : NonEmptyList ε → Validate ε α
  deriving Repr

instance : Functor (Validate ε) where
  map f
   | .ok x => .ok (f x)
   | .errors errs => .errors errs

instance : Applicative (Validate ε) where
  pure := .ok
  seq f x :=
    match f with
    | .ok g => g <$> (x ()) -- Same as `Functor.map g (x ())`
    | .errors errs =>
      match x () with
      | .ok _ => .errors errs
      | .errors errs' => .errors (errs ++ errs')

def Field := String deriving Repr
def reportError (f : Field) (msg : String) : Validate (Field × String) α :=
  .errors { head := (f, msg), tail := [] }

def checkName (name : String) : Validate (Field × String) {n : String // n ≠ ""} :=
  if h : name = "" then
    reportError "name" "Required"
  else pure ⟨name, h⟩

def Validate.andThen (val : Validate ε α) (next : α → Validate ε β) : Validate ε β :=
  match val with
  | .errors errs => .errors errs
  | .ok x => next x

def checkYearIsNat (year : String) : Validate (Field × String) Nat :=
  match year.trim.toNat? with
  | none => reportError "birth year" "Must be digits"
  | some n => pure n

def checkBirthYear (thisYear year : Nat) :
    Validate (Field × String) {y : Nat // y > 1900 ∧ y ≤ thisYear} :=
  if h : year > 1900 then
    if h' : year ≤ thisYear then
      pure ⟨year, by simp [*]⟩
    else reportError "birth year" s!"Must be no later than {thisYear}"
  else reportError "birth year" "Must be after 1900"

def checkYear (yearInput : String) (thisYear : Nat):
    Validate (Field × String) {y : Nat // y > 1900 ∧ y ≤ thisYear} :=
  (checkYearIsNat yearInput).andThen <| checkBirthYear thisYear

def checkInput (year : Nat) (input : RawInput) : Validate (Field × String) (CheckedInput year) :=
  pure CheckedInput.mk <*>
  checkName input.name <*>
  checkYear input.birthYear year

def doubleId (a : α) (b : β) : (α × β) := (a, b)

def tripleId (a : α) (b : β) (c : γ) : (α × β × γ) := (a, b, c)

#eval pure tripleId <*> checkName "potato" <*> checkYear "1999" 2020 <*> checkName "banana"

#eval checkInput 2023 {name := "David", birthYear := "1984"}
#eval checkInput 2023 {name := "", birthYear := "2045"}
