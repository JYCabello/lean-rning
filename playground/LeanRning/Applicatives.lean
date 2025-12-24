structure CheckedInput (thisYear : Nat) : Type where
  name : {n : String // n ≠ ""}
  birthYear : {y : Nat // y > 1900 ∧ y ≤ thisYear}

def validPerson : CheckedInput 2025 :=
  { name := ⟨"Alice", by decide⟩
    birthYear := ⟨1990, by decide⟩
  }

def tryValidPerson (name : String) (year : Nat) : Option (CheckedInput 2025) :=
  if hName : name ≠ "" then
  if hYear : year > 1900 ∧ year ≤ 2025 then
      some { name := ⟨name, hName⟩, birthYear := ⟨year, hYear⟩ }
  else none
  else none

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

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

def Field := String
def reportError (f : Field) (msg : String) : Validate (Field × String) α :=
  .errors { head := (f, msg), tail := [] }
