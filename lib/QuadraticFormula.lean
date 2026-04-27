-- 一元二次方程求根公式推导（仿照人手工推导过程）
-- 例子: x² - 2x - 3 = 0
-- 依赖: Nat, Int, IntOrder, Frac, Algebra, Eq

import Frac
import Algebra
import Eq

-- =====================================================================
-- 1. 定义方程系数
-- =====================================================================
def a := nat_to_frac 1      -- a = 1
def b := int_to_frac (negSucc 1)  -- b = -2
def c := int_to_frac (negSucc 2)  -- c = -3

-- =====================================================================
-- 2. 验证原始方程在 x=3 和 x=-1 时成立
-- =====================================================================

-- 验证 x = 3: 1·3² + (-2)·3 + (-3) = 9 - 6 - 3 = 0
solve verify_x3 : Eq Frac (frac_add (frac_add (frac_mul a (square (nat_to_frac 3))) (frac_mul b (nat_to_frac 3))) c) (nat_to_frac 0) := refl Frac (nat_to_frac 0)

-- 验证 x = -1: 1·(-1)² + (-2)·(-1) + (-3) = 1 + 2 - 3 = 0
solve verify_x_neg1 : Eq Frac (frac_add (frac_add (frac_mul a (square (frac_neg (nat_to_frac 1)))) (frac_mul b (frac_neg (nat_to_frac 1)))) c) (nat_to_frac 0) := refl Frac (nat_to_frac 0)

-- =====================================================================
-- 3. 配方推导步骤
-- =====================================================================

-- 步骤1: 方程两边除以 a (这里 a=1，不变)
-- x² - 2x - 3 = 0

-- 步骤2: 移常数项到右边
-- x² - 2x = 3
-- 验证: x² + (-2)x = 3
solve step2 : Eq Frac (frac_add (square (nat_to_frac 3)) (frac_mul b (nat_to_frac 3))) (nat_to_frac 3) := refl Frac (nat_to_frac 3)

-- 步骤3: 计算配方常数 (b/2a)²
-- b/2a = -2/2 = -1
-- (b/2a)² = (-1)² = 1

-- 定义半系数: b / (2a) = -2 / 2 = -1
def half_b_over_a := frac_div b (frac_mul (nat_to_frac 2) a)

-- 验证半系数等于 -1
def step3_half : Eq Frac half_b_over_a (frac_neg (nat_to_frac 1)) := refl Frac (frac_neg (nat_to_frac 1))

-- 定义配方常数
def complete_sq_term := square half_b_over_a

-- 验证配方常数等于 1
def step3_term : Eq Frac complete_sq_term (nat_to_frac 1) := refl Frac (nat_to_frac 1)

-- 步骤4: 两边加配方常数
-- x² - 2x + 1 = 3 + 1 = 4
-- 验证: 左边在 x=3 时: 9 - 6 + 1 = 4
def step4_left : Eq Frac (frac_add (frac_add (square (nat_to_frac 3)) (frac_mul b (nat_to_frac 3))) complete_sq_term) (nat_to_frac 4) := refl Frac (nat_to_frac 4)

-- 步骤5: 左边写成完全平方
-- (x + b/2a)² = (x - 1)²
-- 验证: (3 - 1)² = 4
def step5_sq : Eq Frac (square (frac_add (nat_to_frac 3) half_b_over_a)) (nat_to_frac 4) := refl Frac (nat_to_frac 4)

-- =====================================================================
-- 4. 判别式与求根公式
-- =====================================================================

-- 判别式 D = b² - 4ac = 4 - 4(1)(-3) = 4 + 12 = 16
def disc := frac_sub (square b) (frac_mul (nat_to_frac 4) (frac_mul a c))

-- 验证判别式等于 16
solve verify_disc : Eq Frac disc (nat_to_frac 16) := refl Frac (nat_to_frac 16)

-- 求根公式: x = (-b ± √D) / 2a
-- 定义 √D = 4（这里 D=16 是完全平方数）
def sqrt_disc := nat_to_frac 4

-- 正根: x₁ = (-b + √D) / 2a = (2 + 4) / 2 = 3
def root_pos := frac_div (frac_add (frac_neg b) sqrt_disc) (frac_mul (nat_to_frac 2) a)

-- 验证正根等于 3
def verify_root_pos : Eq Frac root_pos (nat_to_frac 3) := refl Frac (nat_to_frac 3)

-- 负根: x₂ = (-b - √D) / 2a = (2 - 4) / 2 = -1
def root_neg := frac_div (frac_sub (frac_neg b) sqrt_disc) (frac_mul (nat_to_frac 2) a)

-- 验证负根等于 -1
def verify_root_neg : Eq Frac root_neg (frac_neg (nat_to_frac 1)) := refl Frac (frac_neg (nat_to_frac 1))

-- =====================================================================
-- 5. 最终验证: 两个根都满足原方程
-- =====================================================================

-- 正根验证: a·x₁² + b·x₁ + c = 0
def final_verify_pos : Eq Frac (frac_add (frac_add (frac_mul a (square root_pos)) (frac_mul b root_pos)) c) (nat_to_frac 0) := refl Frac (nat_to_frac 0)

-- 负根验证: a·x₂² + b·x₂ + c = 0
def final_verify_neg : Eq Frac (frac_add (frac_add (frac_mul a (square root_neg)) (frac_mul b root_neg)) c) (nat_to_frac 0) := refl Frac (nat_to_frac 0)
