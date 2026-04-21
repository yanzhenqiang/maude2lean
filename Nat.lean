inductive Nat where
| zero : Nat
| succ : Nat -> Nat

def nat_add (m : Nat) (n : Nat) : Nat :=
  rec.Nat (fun _ => Nat) n (\m' : Nat . \ih : Nat . succ ih) m

def nat_sub (m : Nat) (n : Nat) : Nat :=
  rec.Nat (fun _ => Nat -> Nat)
    (fun n => zero)
    (\m' : Nat . \ih : Nat -> Nat . fun n : Nat =>
      rec.Nat (fun _ => Nat)
        (succ m')
        (fun n' : Nat => fun _ : Nat => ih n')
        n)
    m
    n

def nat_mul (m : Nat) (n : Nat) : Nat :=
  rec.Nat (fun _ => Nat) zero (\m' : Nat . \ih : Nat . nat_add ih n) m

-- Aliases for infix operators
def add := nat_add
def sub := nat_sub
def mul := nat_mul
