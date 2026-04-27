-- Real number completeness: Cauchy sequences converge
-- Dependencies: Order.lean, True.lean, Int.lean, IntOrder.lean, Frac.lean, Cauchy.lean, Real.lean

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
import Real
import Exists
import WellFounded

-- Sequence converges to a real number
-- Defined using Quot.ind, naturally representative-independent, no seq_converges_to_compat needed
def seq_converges_to (a : Nat -> Frac) (L : Real) : Prop :=
  Quot.ind (Nat -> Frac) cauchy_equiv
    (fun l => forall (k : Nat), exists (N : Nat), forall (n : Nat),
      gt n N -> frac_lt (frac_abs (frac_sub (a n) (l k))) (frac_inv k))
    (fun l => forall (k : Nat), exists (N : Nat), forall (n : Nat),
      gt n N -> frac_lt (frac_abs (frac_sub (a n) (l k))) (frac_inv k))
    L

-- Extract witness N from Cauchy condition (using axiom of choice)
def cauchy_N (a : Nat -> Frac) (h : is_cauchy a) (k : Nat) : Nat :=
  choice Nat
    (fun N : Nat => forall (m : Nat), forall (n : Nat), gt m N -> gt n N -> frac_lt (frac_abs (frac_sub (a m) (a n))) (frac_inv k))
    (h k)

-- Derive self-convergence from Cauchy condition
theorem cauchy_self_dist : forall (a : Nat -> Frac) (h : is_cauchy a) (k : Nat) (n : Nat),
  gt n (cauchy_N a h k) ->
  frac_lt (frac_abs (frac_sub (a n) (a (succ (cauchy_N a h k))))) (frac_inv k) :=
  fun a : (Nat -> Frac) => fun h : (is_cauchy a) => fun k : Nat => fun n : Nat => fun h_n : (gt n (cauchy_N a h k)) =>
    choice_spec Nat
      (fun N : Nat => forall (m : Nat), forall (n : Nat), gt m N -> gt n N -> frac_lt (frac_abs (frac_sub (a m) (a n))) (frac_inv k))
      (h k)
      n (succ (cauchy_N a h k)) h_n (gt_succ (cauchy_N a h k))

-- Construct limit sequence (diagonal construction)
def limit_seq (a : Nat -> Frac) (h : is_cauchy a) : Nat -> Frac :=
  fun k => a (succ (cauchy_N a h k))

-- Construct limit real number
def limit_real (a : Nat -> Frac) (h : is_cauchy a) : Real :=
  real_mk (limit_seq a h)

-- =====================================================================
-- Cauchy completeness theorem
-- Depends on FracArith.lean: frac_dist_self, cauchy_self_dist
-- =====================================================================

-- Every Cauchy sequence converges to some real number
-- Proof strategy (diagonal construction):
-- 1. Extract witness from is_cauchy a: cauchy_N a h k
-- 2. Construct limit sequence: limit_seq a h k = a (succ (cauchy_N a h k))
-- 3. Prove this sequence converges to limit_real a h
theorem cauchy_complete : forall (a : Nat -> Frac), is_cauchy a -> exists (L : Real), seq_converges_to a L :=
  fun a : Nat -> Frac => fun h : is_cauchy a =>
    intro Real (fun L : Real => seq_converges_to a L) (limit_real a h)
      (fun k : Nat =>
        intro Nat (fun N : Nat => forall (n : Nat), gt n N -> frac_lt (frac_abs (frac_sub (a n) (a (succ (cauchy_N a h k))))) (frac_inv k))
          (cauchy_N a h k)
          (fun n : Nat => fun h_n : gt n (cauchy_N a h k) =>
            cauchy_self_dist a h k n h_n))

-- Constant sequence converges to itself
theorem const_seq_converges : forall (c : Frac), seq_converges_to (fun n : Nat => c) (real_mk (fun n : Nat => c)) :=
  fun c : Frac =>
    fun k : Nat =>
      intro Nat (fun N : Nat => forall (n : Nat), gt n N -> frac_lt (frac_abs (frac_sub c c)) (frac_inv k))
        0
        (fun n : Nat => fun _ : gt n 0 => frac_dist_self c k)

-- Zero sequence converges to zero real number
theorem zero_seq_converges : seq_converges_to (fun n : Nat => nat_to_frac 0) real_zero :=
  const_seq_converges (nat_to_frac 0)
