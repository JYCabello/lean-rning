def hello := "world"

inductive Maybe (α : Type) : Type
| nothing : Maybe α
| just    : α → Maybe α

def positive (num: Int) : Maybe Nat :=
  match num with
  | Int.ofNat (Nat.succ n) => Maybe.just (n + 1)
  | _                      => Maybe.nothing

#eval positive (5)

inductive NumberGreaterThan (num : Int) : Type
| just (val : Int) (h : val > num) : NumberGreaterThan num
| nothing : NumberGreaterThan num

def greaterThan (num : Int) (val : Int) : NumberGreaterThan num :=
  if   holds: val > num
  then NumberGreaterThan.just val holds
  else NumberGreaterThan.nothing

def greaterThanTen := greaterThan 10

#eval greaterThanTen 15
#eval greaterThanTen 5
