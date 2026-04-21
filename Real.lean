-- 实数：通过柯西序列的商类型构造
-- 依赖: Order.lean, True.lean, Int.lean, IntOrder.lean, Frac.lean, Cauchy.lean

def Real := Quot (Nat -> Frac) cauchy_equiv

def real_mk (a : Nat -> Frac) : Real := Quot.mk (Nat -> Frac) cauchy_equiv a

def real_zero : Real := real_mk (fun n : Nat => nat_to_frac 0)
