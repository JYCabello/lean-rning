def List.sumOfContents [Add α] [Zero α] : List α -> α :=
  λ lst =>
    let rec sum l (acc : α) :=
      match l with
      | [] => acc
      | x :: xs => sum xs (x + acc)
    sum lst Zero.zero

def List.trySumOfContents {α} [Add α] : List α -> Option α :=
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

instance : Add Positive where
  add a b :=
    let rec add' : Positive → Positive → Positive
      | a, Positive.one => Positive.succ a
      | a, Positive.succ b => Positive.succ (add' a b)
    add' a b

instance : ToString Positive where
  toString
    | Positive.one => "1"
    | Positive.succ p =>
      let rec toNat : Positive → Nat
        | Positive.one => 1
        | Positive.succ p => (toNat p) + 1
      toString (toNat (Positive.succ p))

def positives : List Positive := [1, 2, 3]

#eval [1, 2, 3].trySumOfContents
#eval [1.5, 2.5, 3.0].sumOfContents
#eval ([] : List Int).trySumOfContents
#eval positives.trySumOfContents
