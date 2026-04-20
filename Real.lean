-- 实数：通过柯西序列的商类型构造
-- 依赖: Order.lean, True.lean, Int.lean, IntOrder.lean, Frac.lean, Cauchy.lean

def Real := Quot (Nat -> Frac) cauchy_equiv

def real_mk (a : Nat -> Frac) : Real := Quot.mk (Nat -> Frac) cauchy_equiv a

-- =====================================================================
-- 加法兼容性公理
-- 注: 这些引理需要分数算术基础设施（交换律、结合律、三角不等式等）
--     在当前阶段作为公理引入，后续可补全严格证明
-- cauchy_equiv_add_compat_right: 若 b ~ b'，则 a+b ~ a+b'
-- cauchy_equiv_add_compat_left:  若 a ~ a'，则 a+b ~ a'+b
-- =====================================================================

axiom cauchy_equiv_add_compat_right : forall (a : Nat -> Frac) (b b' : Nat -> Frac),
  cauchy_equiv b b' -> cauchy_equiv (frac_add a b) (frac_add a b')

axiom cauchy_equiv_add_compat_left : forall (a a' : Nat -> Frac) (b : Nat -> Frac),
  cauchy_equiv a a' -> cauchy_equiv (frac_add a b) (frac_add a' b)

-- 内层兼容性证明: 对固定的 a，Quot.lift 在第二个参数上兼容
def real_add_inner_compat (a : Nat -> Frac) (b b' : Nat -> Frac)
  (h : cauchy_equiv b b') : Eq Real (real_mk (frac_add a b)) (real_mk (frac_add a b')) :=
  Quot.sound (Nat -> Frac) cauchy_equiv (frac_add a b) (frac_add a b')
    (cauchy_equiv_add_compat_right a b b' h)

-- 辅助函数: a 固定时，对 Real 参数做 Quot.lift
def real_add_f (a : Nat -> Frac) (q : Real) : Real :=
  Quot.lift (Nat -> Frac) cauchy_equiv (fun b => real_mk (frac_add a b))
    (real_add_inner_compat a) q

-- 外层兼容性证明: 使用 Quot.ind 对内层 Quot.lift 做归纳
def real_add_outer_compat (a a' : Nat -> Frac) (y : Real)
  (h : cauchy_equiv a a') : Eq Real (real_add_f a y) (real_add_f a' y) :=
  Quot.ind (Nat -> Frac) cauchy_equiv
    (fun q => Eq Real (real_add_f a q) (real_add_f a' q))
    (fun b => Quot.sound (Nat -> Frac) cauchy_equiv (frac_add a b) (frac_add a' b)
      (cauchy_equiv_add_compat_left a a' b h))
    y

-- 实数加法: 用 Quot.lift 定义，保证与代表元无关
def real_add (x : Real) (y : Real) : Real :=
  Quot.lift (Nat -> Frac) cauchy_equiv (fun a => real_add_f a y)
    (fun a a' h => real_add_outer_compat a a' y h) x

def real_zero : Real := real_mk (fun n : Nat => nat_to_frac 0)

-- 代表元唯一性：等价的柯西序列表示同一个实数
theorem real_mk_eq_of_cauchy_equiv : forall (a : Nat -> Frac), forall (b : Nat -> Frac),
  cauchy_equiv a b -> Eq Real (real_mk a) (real_mk b) :=
  fun a : (Nat -> Frac) => fun b : (Nat -> Frac) => fun h : (cauchy_equiv a b) =>
    Quot.sound (Nat -> Frac) cauchy_equiv a b h
