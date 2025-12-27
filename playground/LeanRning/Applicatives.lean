structure RawInput where
  name : String
  birthYear : String

def NonEmptyString := {n : String // n ≠ ""} deriving Repr
def ValidBirthDate thisYear := {y : Nat // y > 1900 ∧ y ≤ thisYear} deriving Repr

structure CheckedInput (thisYear : Nat) : Type where
  name : NonEmptyString
  birthYear : ValidBirthDate thisYear
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

instance : Coe (α) (NonEmptyList α) where
  coe a := { head := a, tail := [] }

def NonEmptyList.asList (as : NonEmptyList α) :=
  [as.head] ++ as.tail

instance {α} [Repr α] : Repr (NonEmptyList α) where
 reprPrec as _ :=
  as.asList.foldl
    (λ acc a => s!"{acc}{Repr.reprPrec a 0}")
    ""

def NonEmptyList.append (xs ys : NonEmptyList α) : NonEmptyList α :=
  ⟨xs.head, xs.tail ++ [ys.head] ++ ys.tail⟩

instance : Append (NonEmptyList α) where
  append xs ys :=
    { head := xs.head, tail := xs.tail ++ ys.head :: ys.tail }

instance : HAppend (NonEmptyList α) (List α) (NonEmptyList α) where
  hAppend xs ys :=
    { head := xs.head, tail := xs.tail ++ ys }

abbrev Field := String

inductive TreeError where
  | field : Field → String → TreeError
  | path : String → TreeError → TreeError
  | both : TreeError → TreeError → TreeError

instance : Append TreeError where
  append := .both

instance : Repr TreeError where
  reprPrec e _ :=
    let rec render err :=
      match err with
      | .field f msg => s!"  -{f}: {msg}\n"
      | .path p e => s!"{p}:\n{render e}"
      | .both e1 e2 => s!"{render e1}{render e2}"
    render e

def sampleError : TreeError :=
  (TreeError.path "Person" (TreeError.field "name" "Must not be empty"))
   ++ TreeError.field "name" "Cannot include hieroglyphs"
   ++ TreeError.field "name" "Should have some coolness to it"

#eval sampleError

def toTree (path: String) (errs: NonEmptyList (Field × String)) : NonEmptyList TreeError :=
  errs.tail.foldl
      (λ acc err => acc ++ TreeError.field err.fst err.snd)
      (TreeError.path path (TreeError.field errs.head.fst errs.head.snd))

inductive Validate (ε α : Type) : Type where
  | ok : α → Validate ε α
  | errors : ε → Validate ε α
  deriving Repr

instance : Functor (Validate ε) where
  map f
   | .ok x => .ok (f x)
   | .errors errs => .errors errs

instance [Append ε] : Applicative (Validate ε) where
  pure := .ok
  seq f x :=
    match f with
    | .ok g => g <$> (x ()) -- Same as `Functor.map g (x ())`
    | .errors errs =>
      match x () with
      | .ok _ => .errors errs
      | .errors errs' => .errors (errs ++ errs')

def Validate.mapErrors : Validate ε α → (ε → ε') → Validate ε' α
  | .ok a, _ => .ok a
  | .errors err, f => .errors (f err)

abbrev ValidationErrors := (NonEmptyList (Field × String))

abbrev TreeValidationErrors := (NonEmptyList TreeError)

def reportError (f : Field) (msg : String) : Validate ValidationErrors α :=
  .errors { head := (f, msg), tail := [] }

def checkName (name : String) : Validate ValidationErrors NonEmptyString :=
  if h : name = "" then
    reportError "name" "Required"
  else pure ⟨name, h⟩

def Validate.andThen (val : Validate ε α) (next : α → Validate ε β) : Validate ε β :=
  match val with
  | .errors errs => .errors errs
  | .ok x => next x

def checkYearIsNat (year : String) : Validate ValidationErrors Nat :=
  match year.trim.toNat? with
  | none => reportError "birth year" "Must be digits"
  | some n => pure n

def checkBirthYear (thisYear year : Nat) : Validate ValidationErrors (ValidBirthDate thisYear) :=
  if h : year > 1900 then
    if h' : year ≤ thisYear then
      pure ⟨year, by simp [*]⟩
    else reportError "birth year" s!"Must be no later than {thisYear}"
  else reportError "birth year" "Must be after 1900"

def checkYear (yearInput : String) (thisYear : Nat): Validate ValidationErrors (ValidBirthDate thisYear) :=
  (checkYearIsNat yearInput).andThen <| checkBirthYear thisYear

def checkInput (thisYear : Nat) (input : RawInput) : Validate ValidationErrors (CheckedInput thisYear) :=
  pure CheckedInput.mk <*>
  checkName input.name <*>
  checkYear input.birthYear thisYear

def doubleId (a : α) (b : β) : (α × β) := (a, b)
def tripleId (a : α) (b : β) (c : γ) : (α × β × γ) := (a, b, c)

#eval pure tripleId <*> checkName "potato" <*> checkYear "1999" 2020 <*> checkName "banana"

#eval checkInput 2023 {name := "David", birthYear := "1984"}
#eval checkInput 2023 {name := "", birthYear := "2045"}

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

def Validate.orElse
    [Append ε]
    (a : Validate ε α)
    (b : Unit → Validate ε α):
    Validate ε α :=
  match a with
  | .ok x => .ok x
  | .errors errs1 =>
    match b () with
    | .ok x => .ok x
    | .errors errs2 => .errors (errs1 ++ errs2)

instance [Append ε] : OrElse (Validate ε α) where
  orElse := Validate.orElse

def checkThat
    (condition : Bool)
    (field : Field)
    (msg : String)
    : Validate ValidationErrors Unit :=
  if condition then pure () else reportError field msg

def checkCompany (input : RawInput) :  Validate ValidationErrors LegacyCheckedInput :=
  checkThat (input.birthYear == "FIRM") "birth year" "FIRM if a company"
  *> .company
  <$> checkName input.name

def checkSubtype
    {α : Type}
    (v : α)
    (p : α → Prop)
    [Decidable (p v)]
    (err : ε)
    : Validate (NonEmptyList ε) {x : α // p x} :=
  if h : p v then
    pure ⟨v, h⟩
  else
    .errors { head := err, tail := [] }

def checkHumanBefore1970
    (input : RawInput)
    : Validate ValidationErrors LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanBefore1970
    <$> checkSubtype y (fun x => x > 999 ∧ x < 1970) ("birth year", "less than 1970")
    <*> pure input.name

def checkHumanAfter1970
   (input : RawInput)
   : Validate ValidationErrors LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanAfter1970
    <$> checkSubtype y (· > 1970) ("birth year", "greater than 1970")
    <*> checkName input.name

def checkLegacyInput
    (input : RawInput)
    : Validate TreeValidationErrors LegacyCheckedInput :=
  (checkCompany input).mapErrors (λ e => toTree "Company" e)
  <|> (checkHumanBefore1970 input).mapErrors (λ e => toTree "Human born before 1970" e)
  <|> (checkHumanAfter1970 input).mapErrors (λ e => toTree "Human born after 1970" e)

#eval checkLegacyInput ⟨"Johnny's Troll Groomers", "FIRM"⟩
#eval checkLegacyInput ⟨"Johnny", "1963"⟩
#eval checkLegacyInput ⟨"", "1963"⟩
#eval checkLegacyInput ⟨"", "1970"⟩
