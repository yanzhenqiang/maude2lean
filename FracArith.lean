-- 分数算术引理
-- 依赖: Order.lean, True.lean, Int.lean, IntOrder.lean, Frac.lean, NatProof.lean

-- =====================================================================
-- 零分数
-- =====================================================================

def frac_zero : Frac := mk (ofNat 0) 0

-- =====================================================================
-- 整数引理（基于 Int 的 recursor 结构）
-- =====================================================================

-- =====================================================================
-- 手写 recursor 证明示例: int_add_zero_left
-- =====================================================================

-- 目标: 证明 0 + b = b（零是整数加法左单位元）
-- 策略: 对 b 用 rec.Int 归纳

-- int_add 对第一个参数为 ofNat m 时的定义:
--   int_add (ofNat m) (ofNat n) = ofNat (nat_add m n)
--   int_add (ofNat 0) (negSucc n) = negSucc n（因为 m=0 时 rec.Nat 取基础分支）

theorem int_add_zero_left : forall (b : Int), Eq Int (int_add (ofNat 0) b) b :=
  fun b : Int =>
    rec.Int (fun x : Int => Eq Int (int_add (ofNat 0) x) x)
      -- 分支1: b = ofNat n
      -- int_add (ofNat 0) (ofNat n) = ofNat (nat_add 0 n)
      -- 需要证明 ofNat (nat_add 0 n) = ofNat n
      -- 用已有的 nat_add_zero_right: nat_add 0 n = n
      -- 再用 eq_subst 替换
      (fun n : Nat =>
        eq_subst Nat (nat_add 0 n) n
          (fun y : Nat => Eq Int (ofNat (nat_add 0 n)) (ofNat y))
          (nat_add_zero_right n)
          (refl Int (ofNat (nat_add 0 n))))
      -- 分支2: b = negSucc n
      -- int_add (ofNat 0) (negSucc n) = negSucc n（直接由定义归约）
      (fun n : Nat => refl Int (negSucc n))
      b

-- int_mul (ofNat 1) (ofNat n) = ofNat n
theorem int_mul_one_left_ofNat : forall (n : Nat), Eq Int (int_mul (ofNat 1) (ofNat n)) (ofNat n) :=
  fun n : Nat => refl Int (ofNat n)

-- int_abs (ofNat 0) = ofNat 0
theorem int_abs_zero : Eq Int (int_abs (ofNat 0)) (ofNat 0) :=
  refl Int (ofNat 0)

-- 辅助定理: int_add (ofNat (succ n)) (negSucc n) = ofNat 0
theorem int_add_ofNat_negSucc_eq : forall (n : Nat), Eq Int (int_add (ofNat (succ n)) (negSucc n)) (ofNat 0) :=
  fun n : Nat =>
    rec.Nat (fun x : Nat => Eq Int (int_add (ofNat (succ x)) (negSucc x)) (ofNat 0))
      (refl Int (ofNat 0))
      (fun n' : Nat => fun ih : Eq Int (int_add (ofNat (succ n')) (negSucc n')) (ofNat 0) =>
        eq_subst Int (int_add (ofNat (succ n')) (negSucc n')) (ofNat 0)
          (fun y : Int => Eq Int (int_add (ofNat (succ (succ n'))) (negSucc (succ n'))) y)
          ih
          (refl Int (int_add (ofNat (succ n')) (negSucc n'))))
      n

-- 辅助定理: int_add (negSucc n) (ofNat (succ n)) = ofNat 0
theorem int_add_negSucc_ofNat_eq : forall (n : Nat), Eq Int (int_add (negSucc n) (ofNat (succ n))) (ofNat 0) :=
  fun n : Nat =>
    rec.Nat (fun x : Nat => Eq Int (int_add (negSucc x) (ofNat (succ x))) (ofNat 0))
      (refl Int (ofNat 0))
      (fun n' : Nat => fun ih : Eq Int (int_add (negSucc n') (ofNat (succ n'))) (ofNat 0) =>
        eq_subst Int (int_add (negSucc n') (ofNat (succ n'))) (ofNat 0)
          (fun y : Int => Eq Int (int_add (negSucc (succ n')) (ofNat (succ (succ n')))) y)
          ih
          (refl Int (int_add (negSucc n') (ofNat (succ n')))))
      n

-- int_mul a b = int_mul b a（整数乘法交换律）
theorem int_mul_comm : forall (a : Int) (b : Int), Eq Int (int_mul a b) (int_mul b a) :=
  fun a : Int => fun b : Int =>
    rec.Int (fun x : Int => Eq Int (int_mul x b) (int_mul b x))
      (fun m : Nat =>
        rec.Int (fun y : Int => Eq Int (int_mul (ofNat m) y) (int_mul y (ofNat m)))
          (fun n : Nat =>
            eq_subst Nat (nat_mul m n) (nat_mul n m)
              (fun y : Nat => Eq Int (ofNat (nat_mul m n)) (ofNat y))
              (nat_mul_comm m n)
              (refl Int (ofNat (nat_mul m n))))
          (fun n : Nat => refl Int (int_mul (ofNat m) (negSucc n))))
      (fun m : Nat =>
        rec.Int (fun y : Int => Eq Int (int_mul (negSucc m) y) (int_mul y (negSucc m)))
          (fun n : Nat => refl Int (int_mul (negSucc m) (ofNat n)))
          (fun n : Nat =>
            eq_subst Nat (nat_mul (succ m) (succ n)) (nat_mul (succ n) (succ m))
              (fun y : Nat => Eq Int (ofNat (nat_mul (succ m) (succ n))) (ofNat y))
              (nat_mul_comm (succ m) (succ n))
              (refl Int (ofNat (nat_mul (succ m) (succ n))))))
      a

-- int_sub a a = ofNat 0（整数自减为零）
theorem int_sub_self : forall (a : Int), Eq Int (int_sub a a) (ofNat 0) :=
  fun a : Int =>
    rec.Int (fun x : Int => Eq Int (int_sub x x) (ofNat 0))
      (fun n : Nat =>
        rec.Nat (fun x : Nat => Eq Int (int_sub (ofNat x) (ofNat x)) (ofNat 0))
          (refl Int (ofNat 0))
          (fun n' : Nat => fun ih : Eq Int (int_sub (ofNat n') (ofNat n')) (ofNat 0) =>
            eq_subst Int (int_add (ofNat (succ n')) (negSucc n')) (ofNat 0)
              (fun y : Int => Eq Int (int_add (ofNat (succ n')) (int_neg (ofNat (succ n')))) y)
              (int_add_ofNat_negSucc_eq n')
              (refl Int (int_add (ofNat (succ n')) (negSucc n'))))
          n)
      (fun n : Nat =>
        eq_subst Int (int_add (negSucc n) (ofNat (succ n))) (ofNat 0)
          (fun y : Int => Eq Int (int_add (negSucc n) (int_neg (negSucc n))) y)
          (int_add_negSucc_ofNat_eq n)
          (refl Int (int_add (negSucc n) (ofNat (succ n)))))
      a

-- =====================================================================
-- 分数引理
-- =====================================================================

-- frac_mul x y = frac_mul y x（分数乘法交换律）
theorem frac_mul_comm : forall (x : Frac) (y : Frac), Eq Frac (frac_mul x y) (frac_mul y x) :=
  fun x : Frac => fun y : Frac =>
    rec.Frac (fun z : Frac => Eq Frac (frac_mul z y) (frac_mul y z))
      (fun n1 : Int => fun d1 : Nat =>
        rec.Frac (fun w : Frac => Eq Frac (frac_mul (mk n1 d1) w) (frac_mul w (mk n1 d1)))
          (fun n2 : Int => fun d2 : Nat =>
            eq_subst Int (int_mul n1 n2) (int_mul n2 n1)
              (fun y_val : Int => Eq Frac (mk (int_mul n1 n2) (nat_sub (nat_mul (succ d1) (succ d2)) (succ zero))) (mk y_val (nat_sub (nat_mul (succ d2) (succ d1)) (succ zero))))
              (int_mul_comm n1 n2)
              (eq_subst Nat (nat_sub (nat_mul (succ d1) (succ d2)) (succ zero)) (nat_sub (nat_mul (succ d2) (succ d1)) (succ zero))
                (fun y_val : Nat => Eq Frac (mk (int_mul n1 n2) (nat_sub (nat_mul (succ d1) (succ d2)) (succ zero))) (mk (int_mul n2 n1) y_val))
                (eq_subst Nat (nat_mul (succ d1) (succ d2)) (nat_mul (succ d2) (succ d1))
                  (fun y_val : Nat => Eq Nat (nat_sub (nat_mul (succ d1) (succ d2)) (succ zero)) (nat_sub y_val (succ zero)))
                  (nat_mul_comm (succ d1) (succ d2))
                  (refl Nat (nat_sub (nat_mul (succ d1) (succ d2)) (succ zero))))
                (refl Frac (mk (int_mul n1 n2) (nat_sub (nat_mul (succ d1) (succ d2)) (succ zero))))))
          y)
      x

-- frac_sub a a = frac_zero（分数自减为零）
-- 注意: 在当前定义下 frac_sub (mk n d) (mk n d) 的分母为 nat_sub ((d+1)*(d+1)) 1，
-- 只有当 d = 0 时才等于 frac_zero = mk (ofNat 0) 0，所以此定理暂不成立。
-- theorem frac_sub_self : forall (a : Frac), Eq Frac (frac_sub a a) frac_zero := ...

-- frac_abs frac_zero = frac_zero
theorem frac_abs_zero : Eq Frac (frac_abs frac_zero) frac_zero :=
  refl Frac frac_zero

-- frac_abs (mk (ofNat 0) d) = mk (ofNat 0) d（零的绝对值不变）
theorem frac_abs_ofNat_zero : forall (d : Nat), Eq Frac (frac_abs (mk (ofNat 0) d)) (mk (ofNat 0) d) :=
  fun d : Nat => refl Frac (mk (ofNat 0) d)

-- =====================================================================
-- 分数序引理
-- =====================================================================

-- 零小于任意正分数: frac_lt frac_zero (mk (ofNat 1) k) 对所有 k 成立
-- frac_lt (mk 0 0) (mk 1 k) 归约为 le 1 1 = le (succ 0) (succ 0)
theorem frac_lt_zero_one : forall (k : Nat), frac_lt frac_zero (mk (ofNat 1) k) :=
  fun k : Nat => le_succ zero zero (le_zero zero)

-- frac_lt (mk (ofNat 0) d) (mk (ofNat 1) k) 对所有 d, k 成立
-- 归约为 le 1 (succ d) = le (succ 0) (succ d)
theorem frac_lt_zero_pos : forall (d : Nat) (k : Nat), frac_lt (mk (ofNat 0) d) (mk (ofNat 1) k) :=
  fun d : Nat => fun k : Nat => le_succ zero d (le_zero d)

-- frac_lt (frac_abs (frac_sub a a)) (frac_inv k)
-- 真实证明: frac_sub a a 的分子为 int_sub x x = ofNat 0，分母为正
-- frac_abs (mk (ofNat 0) d) = mk (ofNat 0) d
-- frac_lt (mk (ofNat 0) d) (mk (ofNat 1) k) = le 1 (succ d) = le (succ 0) (succ d) = True
theorem frac_dist_self : forall (a : Frac) (k : Nat),
  frac_lt (frac_abs (frac_sub a a)) (frac_inv k) :=
  fun a : Frac => fun k : Nat =>
    rec.Frac (fun x : Frac => frac_lt (frac_abs (frac_sub x x)) (frac_inv k))
      (fun n : Int => fun d : Nat =>
        eq_subst Int (int_sub (int_mul n (ofNat (succ d))) (int_mul n (ofNat (succ d)))) (ofNat 0)
          (fun y : Int => frac_lt (frac_abs (mk y (nat_sub (nat_mul (succ d) (succ d)) (succ zero)))) (frac_inv k))
          (int_sub_self (int_mul n (ofNat (succ d))))
          (eq_subst Int (int_abs (ofNat 0)) (ofNat 0)
            (fun y : Int => frac_lt (mk y (nat_sub (nat_mul (succ d) (succ d)) (succ zero))) (frac_inv k))
            (int_abs_zero)
            (le_succ zero d (le_zero d))))
      a

-- =====================================================================
-- 柯西序列距离引理
-- =====================================================================

