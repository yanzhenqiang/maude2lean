-- 柯西序列定义
-- 依赖: Order.lean, True.lean, Int.lean, IntOrder.lean, Frac.lean
-- 注意: 当前内核中 Pi(x:A).Prop : Type，所以 is_cauchy 的类型是 Type

import Nat
import Eq
import Order
import True
import Int
import IntOrder
import Frac
import NatProof
import FracArith

-- 序列 a : Nat -> Frac 是柯西的，如果：
-- forall (k : Nat), exists (N : Nat), forall (m : Nat), forall (n : Nat),
--   m > N -> n > N -> |a_m - a_n| < 1/(k+1)
def is_cauchy (a : Nat -> Frac) : Prop :=
  forall (k : Nat), exists (N : Nat), forall (m : Nat), forall (n : Nat),
    gt m N -> gt n N -> frac_lt (frac_abs (frac_sub (a m) (a n))) (frac_inv k)

-- 两个序列等价（表示同一个实数）
def cauchy_equiv (a : Nat -> Frac) (b : Nat -> Frac) : Prop :=
  forall (k : Nat), exists (N : Nat), forall (n : Nat),
    gt n N -> frac_lt (frac_abs (frac_sub (a n) (b n))) (frac_inv k)

-- 零序列是柯西的
-- 证明: |0 - 0| = 0 < 1/(k+1) 对所有 k 成立
-- N = 0 即可
def zero_seq_cauchy : is_cauchy (fun n : Nat => nat_to_frac 0) :=
  fun k : Nat =>
    intro Nat (fun N : Nat => forall (m : Nat), forall (n : Nat), gt m N -> gt n N -> le 1 2)
      0
      (fun m : Nat => fun n : Nat => fun h1 : gt m 0 => fun h2 : gt n 0 => le_succ 0 1 (le_zero 1))

