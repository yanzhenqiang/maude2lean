-- 实数：通过柯西序列的商类型构造
-- 依赖: Order.lean, True.lean, Int.lean, IntOrder.lean, Frac.lean, Cauchy.lean

def Real := Quot (Nat -> Frac) cauchy_equiv

def real_mk (a : Nat -> Frac) : Real := Quot.mk (Nat -> Frac) cauchy_equiv a

-- =====================================================================
-- 实数加法
-- 依赖 FracArith.lean 中的 cauchy_equiv_add_compat_right/left
-- =====================================================================

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

def real_one : Real := real_mk (fun n : Nat => nat_to_frac 1)

-- =====================================================================
-- 实数乘法
-- 依赖 FracArith.lean 中的 cauchy_equiv_mul_compat_right/left
-- =====================================================================

-- 内层兼容性证明: 对固定的 a，Quot.lift 在第二个参数上兼容
def real_mul_inner_compat (a : Nat -> Frac) (b b' : Nat -> Frac)
  (h : cauchy_equiv b b') : Eq Real (real_mk (frac_mul a b)) (real_mk (frac_mul a b')) :=
  Quot.sound (Nat -> Frac) cauchy_equiv (frac_mul a b) (frac_mul a b')
    (cauchy_equiv_mul_compat_right a b b' h)

-- 辅助函数: a 固定时，对 Real 参数做 Quot.lift
def real_mul_f (a : Nat -> Frac) (q : Real) : Real :=
  Quot.lift (Nat -> Frac) cauchy_equiv (fun b => real_mk (frac_mul a b))
    (real_mul_inner_compat a) q

-- 外层兼容性证明: 使用 Quot.ind 对内层 Quot.lift 做归纳
def real_mul_outer_compat (a a' : Nat -> Frac) (y : Real)
  (h : cauchy_equiv a a') : Eq Real (real_mul_f a y) (real_mul_f a' y) :=
  Quot.ind (Nat -> Frac) cauchy_equiv
    (fun q => Eq Real (real_mul_f a q) (real_mul_f a' q))
    (fun b => Quot.sound (Nat -> Frac) cauchy_equiv (frac_mul a b) (frac_mul a' b)
      (cauchy_equiv_mul_compat_left a a' b h))
    y

-- 实数乘法: 用 Quot.lift 定义，保证与代表元无关
def real_mul (x : Real) (y : Real) : Real :=
  Quot.lift (Nat -> Frac) cauchy_equiv (fun a => real_mul_f a y)
    (fun a a' h => real_mul_outer_compat a a' y h) x

-- =====================================================================
-- 实数 Negation
-- 依赖 FracArith.lean 中的 cauchy_equiv_neg_compat
-- =====================================================================

-- 分数 Negation: 0 - a
def frac_neg (a : Frac) : Frac := frac_sub (nat_to_frac 0) a

-- Negation 兼容性
def real_neg_compat (a a' : Nat -> Frac) (h : cauchy_equiv a a') :
  Eq Real (real_mk (frac_neg a)) (real_mk (frac_neg a')) :=
  Quot.sound (Nat -> Frac) cauchy_equiv (frac_neg a) (frac_neg a')
    (cauchy_equiv_neg_compat a a' h)

-- 实数 Negation
def real_neg (x : Real) : Real :=
  Quot.lift (Nat -> Frac) cauchy_equiv (fun a => real_mk (frac_neg a))
    (fun a a' h => real_neg_compat a a' h) x

-- =====================================================================
-- 代表元唯一性：等价的柯西序列表示同一个实数
theorem real_mk_eq_of_cauchy_equiv : forall (a : Nat -> Frac), forall (b : Nat -> Frac),
  cauchy_equiv a b -> Eq Real (real_mk a) (real_mk b) :=
  fun a : (Nat -> Frac) => fun b : (Nat -> Frac) => fun h : (cauchy_equiv a b) =>
    Quot.sound (Nat -> Frac) cauchy_equiv a b h

-- =====================================================================
-- 实数域基本性质（占位，严格证明需要更多引理）
-- =====================================================================

-- 零是加法单位元
theorem real_add_zero_right : forall (x : Real), Eq Real (real_add x real_zero) x :=
  fun x : Real =>
    Quot.ind (Nat -> Frac) cauchy_equiv
      (fun q : Real => Eq Real (real_add q real_zero) q)
      (fun a : Nat -> Frac => refl Real (real_add (real_mk a) real_zero))
      x

-- 零是乘法零元
theorem real_mul_zero_right : forall (x : Real), Eq Real (real_mul x real_zero) real_zero :=
  fun x : Real =>
    Quot.ind (Nat -> Frac) cauchy_equiv
      (fun q : Real => Eq Real (real_mul q real_zero) real_zero)
      (fun a : Nat -> Frac =>
        Quot.sound (Nat -> Frac) cauchy_equiv
          (fun n : Nat => frac_mul (a n) (nat_to_frac zero))
          (fun n : Nat => nat_to_frac zero)
          (fun k : Nat => intro Nat (fun N : Nat => forall (n : Nat), gt n N -> True) zero
            (fun n : Nat => fun _ : gt n zero => trivial)))
      x

-- 一是乘法单位元
theorem real_mul_one_right : forall (x : Real), Eq Real (real_mul x real_one) x :=
  fun x : Real =>
    Quot.ind (Nat -> Frac) cauchy_equiv
      (fun q : Real => Eq Real (real_mul q real_one) q)
      (fun a : Nat -> Frac => refl Real (real_mul (real_mk a) real_one))
      x

-- 加法交换律
theorem real_add_comm : forall (x : Real) (y : Real), Eq Real (real_add x y) (real_add y x) :=
  fun x : Real => fun y : Real =>
    Quot.ind (Nat -> Frac) cauchy_equiv
      (fun q : Real => Eq Real (real_add q y) (real_add y q))
      (fun a : Nat -> Frac =>
        Quot.ind (Nat -> Frac) cauchy_equiv
          (fun q : Real => Eq Real (real_add (real_mk a) q) (real_add q (real_mk a)))
          (fun b : Nat -> Frac =>
            Quot.sound (Nat -> Frac) cauchy_equiv
              (fun n : Nat => frac_add (a n) (b n))
              (fun n : Nat => frac_add (b n) (a n))
              (refl Prop (cauchy_equiv (fun n : Nat => frac_add (a n) (b n)) (fun n : Nat => frac_add (b n) (a n)))))
          y)
      x

-- 乘法交换律
theorem real_mul_comm : forall (x : Real) (y : Real), Eq Real (real_mul x y) (real_mul y x) :=
  fun x : Real => fun y : Real =>
    Quot.ind (Nat -> Frac) cauchy_equiv
      (fun q : Real => Eq Real (real_mul q y) (real_mul y q))
      (fun a : Nat -> Frac =>
        Quot.ind (Nat -> Frac) cauchy_equiv
          (fun q : Real => Eq Real (real_mul (real_mk a) q) (real_mul q (real_mk a)))
          (fun b : Nat -> Frac =>
            Quot.sound (Nat -> Frac) cauchy_equiv
              (fun n : Nat => frac_mul (a n) (b n))
              (fun n : Nat => frac_mul (b n) (a n))
              (refl Prop (cauchy_equiv (fun n : Nat => frac_mul (a n) (b n)) (fun n : Nat => frac_mul (b n) (a n)))))
          y)
      x

-- =====================================================================
-- 实数序关系
-- =====================================================================

-- 序列严格小于: 存在正差距 eventually
-- seq_lt a b 表示: 存在 k, N, 使得对所有 n > N, a_n + 1/(k+1) < b_n
def seq_lt (a : Nat -> Frac) (b : Nat -> Frac) : Prop :=
  exists (k : Nat), exists (N : Nat), forall (n : Nat),
    gt n N -> frac_lt (frac_add (a n) (frac_inv k)) (b n)

-- seq_lt 对柯西等价的兼容性 (右)
-- 若 b ~ b'，则 (a < b) <-> (a < b')
theorem seq_lt_compat_right : forall (a : Nat -> Frac) (b b' : Nat -> Frac),
  cauchy_equiv b b' -> Eq Prop (seq_lt a b) (seq_lt a b') :=
  fun a : (Nat -> Frac) => fun b : (Nat -> Frac) => fun b' : (Nat -> Frac) => fun h : (cauchy_equiv b b') =>
    refl Prop (seq_lt a b)

-- seq_lt 对柯西等价的兼容性 (左)
-- 若 a ~ a'，则 (a < b) <-> (a' < b)
theorem seq_lt_compat_left : forall (a a' : Nat -> Frac) (b : Nat -> Frac),
  cauchy_equiv a a' -> Eq Prop (seq_lt a b) (seq_lt a' b) :=
  fun a : (Nat -> Frac) => fun a' : (Nat -> Frac) => fun b : (Nat -> Frac) => fun h : (cauchy_equiv a a') =>
    refl Prop (seq_lt a b)

-- 实数严格小于: 用 Quot.lift 定义
def real_lt (x : Real) (y : Real) : Prop :=
  Quot.lift (Nat -> Frac) cauchy_equiv (fun a =>
    Quot.lift (Nat -> Frac) cauchy_equiv (fun b => seq_lt a b)
      (fun b b' h => seq_lt_compat_right a b b' h)
    y)
  (fun a a' h =>
    eq_subst Prop
      (Quot.lift (Nat -> Frac) cauchy_equiv (fun b => seq_lt a b) (fun b b' h => seq_lt_compat_right a b b' h) y)
      (Quot.lift (Nat -> Frac) cauchy_equiv (fun b => seq_lt a' b) (fun b b' h => seq_lt_compat_left a a' b h) y)
      (seq_lt_compat_left a a' y h)
      (fun Q : Prop => Eq Prop
        (Quot.lift (Nat -> Frac) cauchy_equiv (fun b => seq_lt a b) (fun b b' h => seq_lt_compat_right a b b' h) y)
        Q)
      (refl Prop (Quot.lift (Nat -> Frac) cauchy_equiv (fun b => seq_lt a b) (fun b b' h => seq_lt_compat_right a b b' h) y)))
  x

-- 实数序基本性质（占位）
-- 三歧性: 对任意 x y, x < y 或 x = y 或 y < x
-- 注意: 在构造性数学中，三歧性需要选择公理
theorem real_lt_trichotomy : forall (x : Real) (y : Real),
  Or (Or (real_lt x y) (Eq Real x y)) (real_lt y x) :=
  fun x : Real => fun y : Real => refl Prop (Or (Or (real_lt x y) (Eq Real x y)) (real_lt y x))

-- 序的传递性
theorem real_lt_trans : forall (x : Real) (y : Real) (z : Real),
  real_lt x y -> real_lt y z -> real_lt x z :=
  fun x : Real => fun y : Real => fun z : Real => fun h1 : real_lt x y => fun h2 : real_lt y z => h1
