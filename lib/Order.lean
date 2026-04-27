-- Order relations on Nat (inductive family)
-- le m n means m <= n

import Nat

inductive le : Nat -> Nat -> Prop where
| le_zero : forall (n : Nat), le zero n
| le_succ : forall (m : Nat), forall (n : Nat), le m n -> le (succ m) (succ n)

-- Other order relations defined from le
def lt (m : Nat) (n : Nat) : Prop := le (succ m) n
def ge (m : Nat) (n : Nat) : Prop := le n m
def gt (m : Nat) (n : Nat) : Prop := lt n m

-- Absolute value on Nat (simple version: since Nat has no negatives, abs is identity)
def abs_nat (n : Nat) : Nat := n
