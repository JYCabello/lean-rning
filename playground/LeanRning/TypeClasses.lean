def List.sumOfContents [Add α] [zero : Zero α] : List α -> α :=
  λ lst =>
    let rec sum l (acc : α) :=
      match l with
      | [] => acc
      | x :: xs => sum xs (x + acc)
    sum lst zero.zero

def List.trySumOfContents [Add α] : List α -> Option α :=
  λ lst =>
    let rec sum l (acc : Option α) :=
      match l with
      | x :: xs => sum xs (
        match acc with
        | none   => some x
        | some a => some (a + x)
      )
      | []      => acc
    sum lst none

inductive Positive : Type where
  | one  : Positive
  | succ : Positive → Positive

instance : OfNat Positive (n + 1) where
  ofNat :=
    let rec getNat : Nat → Positive
      | 0 => Positive.one
      | k + 1 => Positive.succ (getNat k)
    getNat n

def positives : List Positive := [1, 2, 3]

#eval [1, 2, 3].trySumOfContents
#eval [1.5, 2.5, 3.0].sumOfContents
#eval ([] : List Int).trySumOfContents
#eval positives.trySumOfContents
