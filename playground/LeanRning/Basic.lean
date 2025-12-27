import Std.Tactic.Do

def hello := "world"

inductive Maybe (α : Type) : Type
| nothing : Maybe α
| just    : α → Maybe α

def positive (num: Int) : Maybe Nat :=
  match num with
  | Int.ofNat (Nat.succ n) => Maybe.just (n + 1)
  | _                      => Maybe.nothing

#eval positive (5)

abbrev IsGreaterThan (num : Int) (val: Int) : Prop := val > num

inductive NumberGreaterThan (num : Int) : Type
| just (val : Int) (h : IsGreaterThan num val) : NumberGreaterThan num

instance : Repr (NumberGreaterThan num) where
  reprPrec x _ := match x with
    | NumberGreaterThan.just val _ => s!"Number {val} is greater than {num}"

def greaterThan (num : Int) (val : Int) : Option (NumberGreaterThan num) :=
  if   h: IsGreaterThan num val
  then some <| NumberGreaterThan.just val h
  else none

def greaterThanPatterned (num : Int) (val : Int) : Option (NumberGreaterThan num) :=
  match h : num < val |> decide with
  | true  => some <| NumberGreaterThan.just val (of_decide_eq_true h)
  | false => none

def matchesProp
    (num : Int)
    (val : Int)
    (property : Int → Int → Prop)
    (constructor : {x : Int // property num x} → β)
    [Decidable (property num val)]
    : (Option β) :=
   if h : property num val then some (constructor ⟨val, h⟩) else none

def greaterThanWithPropAbstraction (num : Int) (val : Int) : Option (NumberGreaterThan num) :=
  matchesProp num val (λ n v => (n < v)) (fun x => NumberGreaterThan.just x.val x.property)

def greaterThanTen := greaterThan 10

#eval greaterThanTen 15
#eval greaterThanTen 5

def greatererThanTen := greaterThanWithPropAbstraction 10

#eval greatererThanTen 15
#eval greatererThanTen 5
