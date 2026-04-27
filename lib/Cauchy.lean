-- Cauchy sequence definition
-- Dependencies: Order.lean, True.lean, Int.lean, IntOrder.lean, Frac.lean
-- Note: In the current kernel Pi(x:A).Prop : Type, so is_cauchy has type Type

import Nat
import Eq
import Order
import True
import Int
import IntOrder
import Frac
import NatProof
import FracArith

-- A sequence a : Nat -> Frac is Cauchy if:
-- forall (k : Nat), exists (N : Nat), forall (m : Nat), forall (n : Nat),
--   m > N -> n > N -> |a_m - a_n| < 1/(k+1)
def is_cauchy (a : Nat -> Frac) : Prop :=
  forall (k : Nat), exists (N : Nat), forall (m : Nat), forall (n : Nat),
    gt m N -> gt n N -> frac_lt (frac_abs (frac_sub (a m) (a n))) (frac_inv k)

-- Two sequences are equivalent (represent the same real number)
def cauchy_equiv (a : Nat -> Frac) (b : Nat -> Frac) : Prop :=
  forall (k : Nat), exists (N : Nat), forall (n : Nat),
    gt n N -> frac_lt (frac_abs (frac_sub (a n) (b n))) (frac_inv k)

-- The zero sequence is Cauchy
-- Proof: |0 - 0| = 0 < 1/(k+1) for all k
-- N = 0 suffices
def zero_seq_cauchy : is_cauchy (fun n : Nat => nat_to_frac 0) :=
  fun k : Nat =>
    intro Nat (fun N : Nat => forall (m : Nat), forall (n : Nat), gt m N -> gt n N -> le 1 2)
      0
      (fun m : Nat => fun n : Nat => fun h1 : gt m 0 => fun h2 : gt n 0 => le_succ 0 1 (le_zero 1))
