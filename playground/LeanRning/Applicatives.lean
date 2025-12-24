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
