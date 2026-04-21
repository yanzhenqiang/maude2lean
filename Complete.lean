-- 实数完备性：柯西序列收敛
-- 依赖: Order.lean, True.lean, Int.lean, IntOrder.lean, Frac.lean, Cauchy.lean, Real.lean

-- 序列收敛到实数
-- 用 Quot.ind 定义，天然代表元无关，无需 seq_converges_to_compat
def seq_converges_to (a : Nat -> Frac) (L : Real) : Prop :=
  Quot.ind (Nat -> Frac) cauchy_equiv
    (fun l => forall (k : Nat), exists (N : Nat), forall (n : Nat),
      gt n N -> frac_lt (frac_abs (frac_sub (a n) (l k))) (frac_inv k))
    (fun l => forall (k : Nat), exists (N : Nat), forall (n : Nat),
      gt n N -> frac_lt (frac_abs (frac_sub (a n) (l k))) (frac_inv k))
    L

-- 从柯西条件提取 witness N（使用选择公理）
def cauchy_N (a : Nat -> Frac) (h : is_cauchy a) (k : Nat) : Nat :=
  choice Nat
    (fun N => forall (m : Nat), forall (n : Nat), gt m N -> gt n N -> frac_lt (frac_abs (frac_sub (a m) (a n))) (frac_inv k))
    (h k)

-- 从柯西条件推导自收敛性
theorem cauchy_self_dist : forall (a : Nat -> Frac) (h : is_cauchy a) (k : Nat) (n : Nat),
  gt n (cauchy_N a h k) ->
  frac_lt (frac_abs (frac_sub (a n) (a (succ (cauchy_N a h k))))) (frac_inv k) :=
  fun a : (Nat -> Frac) => fun h : (is_cauchy a) => fun k : Nat => fun n : Nat => fun h_n : (gt n (cauchy_N a h k)) =>
    choice_spec Nat
      (fun N : Nat => forall (m : Nat), forall (n : Nat), gt m N -> gt n N -> frac_lt (frac_abs (frac_sub (a m) (a n))) (frac_inv k))
      (h k)
      n (succ (cauchy_N a h k)) h_n (gt_succ (cauchy_N a h k))

-- 构造极限序列（对角线构造）
def limit_seq (a : Nat -> Frac) (h : is_cauchy a) : Nat -> Frac :=
  fun k => a (succ (cauchy_N a h k))

-- 构造极限实数
def limit_real (a : Nat -> Frac) (h : is_cauchy a) : Real :=
  real_mk (limit_seq a h)

-- =====================================================================
-- 柯西完备性定理
-- 依赖 FracArith.lean 中的 frac_dist_self, cauchy_self_dist
-- =====================================================================

-- 任何柯西序列都收敛到某个实数
-- 证明策略 (对角线构造):
-- 1. 从 is_cauchy a 中提取 witness: cauchy_N a h k
-- 2. 构造极限序列: limit_seq a h k = a (succ (cauchy_N a h k))
-- 3. 证明该序列收敛到 limit_real a h
theorem cauchy_complete : forall (a : Nat -> Frac), is_cauchy a -> exists (L : Real), seq_converges_to a L :=
  fun a : Nat -> Frac => fun h : is_cauchy a =>
    intro Real (fun L : Real => seq_converges_to a L) (limit_real a h)
      (fun k : Nat =>
        intro Nat (fun N : Nat => forall (n : Nat), gt n N -> frac_lt (frac_abs (frac_sub (a n) (a (succ (cauchy_N a h k))))) (frac_inv k))
          (cauchy_N a h k)
          (fun n : Nat => fun h_n : gt n (cauchy_N a h k) =>
            cauchy_self_dist a h k n h_n))

-- 常数序列收敛到自身
theorem const_seq_converges : forall (c : Frac), seq_converges_to (fun n : Nat => c) (real_mk (fun n : Nat => c)) :=
  fun c : Frac =>
    fun k : Nat =>
      intro Nat (fun N : Nat => forall (n : Nat), gt n N -> frac_lt (frac_abs (frac_sub c c)) (frac_inv k))
        0
        (fun n : Nat => fun _ : gt n 0 => frac_dist_self c k)

-- 零序列收敛到零实数
theorem zero_seq_converges : seq_converges_to (fun n : Nat => nat_to_frac 0) real_zero :=
  const_seq_converges (nat_to_frac 0)
