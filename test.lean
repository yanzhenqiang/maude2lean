inductive Bool where
| true : Bool
| false : Bool

def not (b : Bool) : Bool :=
  match b : Bool with
  | true => false
  | false => true
