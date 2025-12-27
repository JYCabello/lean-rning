import Std.Tactic.Do

def hello := "world"

inductive Maybe (α : Type) : Type
| nothing : Maybe α
| just    : α → Maybe α

def positive (num: Int) : Maybe Nat :=
  match num with
  | Int.ofNat (Nat.succ n) => Maybe.just (n + 1)
  | _                      => Maybe.nothing

#eval positive 5

abbrev IsGreaterThan (num : Int) (val: Int) : Prop := val > num

inductive NumberGreaterThan (num : Int) : Type
| just (val : {x: Int // IsGreaterThan num x }) : NumberGreaterThan num

instance : Repr (NumberGreaterThan num) where
  reprPrec x _ := match x with
    | NumberGreaterThan.just ⟨val, _⟩ => s!"Number {val} is greater than {num}"

def greaterThan (num : Int) (val : Int) : Option (NumberGreaterThan num) :=
  if   h: IsGreaterThan num val
  then NumberGreaterThan.just ⟨val, h⟩
  else none

def greaterThanPatterned (num : Int) (val : Int) : Option (NumberGreaterThan num) :=
  match h : num < val |> decide with
  | true  => NumberGreaterThan.just ⟨val, (of_decide_eq_true h)⟩
  | false => none

-- Meant to understand how to pass props as arguments.
def matchesProp
    (comparand : α)
    (value : β)
    (prop : α → β → Prop)
    (ctor : {val' : β // prop comparand val'} → γ)
    [Decidable (prop comparand value)]
    : (Option γ) :=
   if holds : prop comparand value then ctor ⟨value, holds⟩ else none

def greaterThanPassingProp (gt : Int) (val : Int) : Option (NumberGreaterThan gt) :=
  matchesProp gt val (· < ·) NumberGreaterThan.just

def greaterThanTen := greaterThan 10

#eval greaterThanTen 15
#eval greaterThanTen 5

def greatererThanTen := greaterThanPassingProp 10

#eval greatererThanTen 15
#eval greatererThanTen 5
