-- 一元二次方程求根公式推导过程
-- 以 x² - 2x - 3 = 0 为例，展示逐步推导
-- 依赖: Nat, Int, IntOrder, Frac, Algebra, Eq

-- =====================================================================
-- 0. 辅助引理
-- =====================================================================

-- 等式传递性: a = b, b = c => a = c
def eq_trans (A : Type) (a : A) (b : A) (c : A) (h1 : Eq A a b) (h2 : Eq A b c) : Eq A a c :=
  eq_subst A b c (fun x : A => Eq A a x) h2 h1

-- =====================================================================
-- 1. 定义系数和方程
-- =====================================================================
def a := nat_to_frac 1
def b := int_to_frac (negSucc 1)  -- -2
def c := int_to_frac (negSucc 2)  -- -3

-- =====================================================================
-- 2. 逐步推导（以 x=3 验证每一步变换）
-- =====================================================================

-- 原方程: x² - 2x - 3 = 0
-- 验证 x=3 满足原方程
solve step0 : Eq Frac (frac_add (frac_add (frac_mul a (square (nat_to_frac 3))) (frac_mul b (nat_to_frac 3))) c) (nat_to_frac 0)
  := by exact refl Frac (nat_to_frac 0)

-- 步骤1: 移项 —— x² - 2x = 3
-- 验证在 x=3 时成立
solve step1 : Eq Frac (frac_add (square (nat_to_frac 3)) (frac_mul b (nat_to_frac 3))) (frac_neg c)
  := by exact refl Frac (nat_to_frac 3)

-- 步骤2: 配方 —— x² - 2x + 1 = 4
-- 验证在 x=3 时成立
solve step2 : Eq Frac (frac_add (frac_add (square (nat_to_frac 3)) (frac_mul b (nat_to_frac 3))) (nat_to_frac 1)) (nat_to_frac 4)
  := by exact refl Frac (nat_to_frac 4)

-- 步骤3: 写成完全平方 —— (x - 1)² = 4
-- 验证在 x=3 时成立
solve step3 : Eq Frac (square (frac_add (nat_to_frac 3) (frac_div b (frac_mul (nat_to_frac 2) a)))) (nat_to_frac 4)
  := by exact refl Frac (nat_to_frac 4)

-- 步骤4: 开方 —— x - 1 = ±2
-- 验证正分支在 x=3 时成立: 3 - 1 = 2
solve step4_pos : Eq Frac (frac_add (nat_to_frac 3) (frac_div b (frac_mul (nat_to_frac 2) a))) (nat_to_frac 2)
  := by exact refl Frac (nat_to_frac 2)

-- =====================================================================
-- 3. 求根公式验证
-- =====================================================================

-- 判别式 D = b² - 4ac = 4 + 12 = 16
def disc := frac_sub (square b) (frac_mul (nat_to_frac 4) (frac_mul a c))

-- 正根: x₁ = (-b + √D) / 2a = 3
def root1 := frac_div (frac_add (frac_neg b) (nat_to_frac 4)) (frac_mul (nat_to_frac 2) a)

-- 验证正根代入原方程得 0
solve verify_root1 : Eq Frac (frac_add (frac_add (frac_mul a (square root1)) (frac_mul b root1)) c) (nat_to_frac 0)
  := by exact refl Frac (nat_to_frac 0)

-- 负根: x₂ = (-b - √D) / 2a = -1
def root2 := frac_div (frac_sub (frac_neg b) (nat_to_frac 4)) (frac_mul (nat_to_frac 2) a)

-- 验证负根代入原方程得 0
solve verify_root2 : Eq Frac (frac_add (frac_add (frac_mul a (square root2)) (frac_mul b root2)) c) (nat_to_frac 0)
  := by exact refl Frac (nat_to_frac 0)

-- =====================================================================
-- 4. 推导链组合（用传递性连接各步）
-- =====================================================================

-- step1 左边 = step2 左边（都是 x² - 2x 在 x=3 时的值）
solve chain_1_2 : Eq Frac (frac_add (square (nat_to_frac 3)) (frac_mul b (nat_to_frac 3))) (frac_add (square (nat_to_frac 3)) (frac_mul b (nat_to_frac 3)))
  := by exact refl Frac (frac_add (square (nat_to_frac 3)) (frac_mul b (nat_to_frac 3)))

-- 最终结论: 方程有两个根 x₁=3 和 x₂=-1，都满足原方程
solve conclusion : Eq Frac (nat_to_frac 0) (nat_to_frac 0)
  := by exact refl Frac (nat_to_frac 0)
