inductive Digit where
| d0 : Digit | d1 : Digit | d2 : Digit | d3 : Digit | d4 : Digit
| d5 : Digit | d6 : Digit | d7 : Digit | d8 : Digit | d9 : Digit

inductive Bool where | false : Bool | true : Bool

inductive Nat where | zero : Nat | succ : Nat -> Nat

def not (b : Bool) : Bool := match b : Bool with | true => false | false => true

def nat_to_dec (n : Nat) : Nat := n

inductive List (A : Type) where
| nil : List A
| cons : A -> List A -> List A

def list_length (A : Type) (xs : List A) : Nat :=
  rec.List A (fun _ => Nat) zero (fun x xs ih => succ ih) xs

def list_append (A : Type) (xs ys : List A) : List A :=
  rec.List A (fun _ => List A) ys (fun x xs ih => cons A x ih) xs

def list_filter (A : Type) (p : A -> Bool) (xs : List A) : List A :=
  rec.List A (fun _ => List A) (nil A)
    (fun x xs ih => match p x : List A with
      | true => cons A x ih
      | false => ih)
    xs

-- correct Nat comparison
def nat_le (m n : Nat) : Bool :=
  rec.Nat (fun _ => Nat -> Bool)
    (fun n => true)
    (fun m' ih => fun n =>
      rec.Nat (fun _ => Bool)
        false
        (fun n' ih2 => ih n')
        n)
    m
    n

def dec_le (a b : Nat) : Bool := nat_le a b

def quicksort_fuel (A : Type) (le : A -> A -> Bool) (fuel : Nat) (xs : List A) : List A :=
  rec.Nat (fun _ => List A -> List A)
    (fun xs => xs)
    (fun fuel' ih => fun xs =>
      rec.List A (fun _ => List A)
        (nil A)
        (fun head tail _ =>
          list_append A (ih (list_filter A (fun x => le x head) tail))
            (cons A head (ih (list_filter A (fun x => le head x) tail))))
        xs)
    fuel
    xs

def quicksort (A : Type) (le : A -> A -> Bool) (xs : List A) : List A :=
  quicksort_fuel A le (list_length A xs) xs

-- 3 elements
def e0 : Nat := 3
def e1 : Nat := 1
def e2 : Nat := 2

def input_list : List Nat :=
  cons Nat e0 (cons Nat e1 (cons Nat e2 (nil Nat)))
