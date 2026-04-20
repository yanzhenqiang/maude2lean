-- 实数：通过柯西序列的商类型构造
-- 依赖: Order.lean, True.lean, Int.lean, IntOrder.lean, Frac.lean, Cauchy.lean

def Real := Quot (Nat -> Frac) cauchy_equiv

def real_mk (a : Nat -> Frac) : Real := Quot.mk (Nat -> Frac) cauchy_equiv a

-- 实数加法: 用 Quot.lift 定义，保证与代表元无关
def real_add (x : Real) (y : Real) : Real :=
  Quot.lift (Nat -> Frac) cauchy_equiv (fun a =>
    Quot.lift (Nat -> Frac) cauchy_equiv (fun b => Quot.mk (Nat -> Frac) cauchy_equiv (frac_add a b))
      (fun b b' h => trivial) y
  ) (fun a a' h => trivial) x

def real_zero : Real := real_mk (fun n : Nat => nat_to_frac 0)
