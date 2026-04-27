-- Real numbers: constructed as quotient of Cauchy sequences
-- Dependencies: Order.lean, True.lean, Int.lean, IntOrder.lean, Frac.lean, Cauchy.lean

import Nat
import Eq
import Order
import True
import Int
import IntOrder
import Frac
import NatProof
import FracArith
import Cauchy

def Real := Quot (Nat -> Frac) cauchy_equiv

def real_mk (a : Nat -> Frac) : Real := Quot.mk (Nat -> Frac) cauchy_equiv a

def real_zero : Real := real_mk (fun n : Nat => nat_to_frac 0)
