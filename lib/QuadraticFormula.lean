-- Quadratic formula derivation (mimicking human manual derivation)
-- Example: x^2 - 2x - 3 = 0
-- Dependencies: Nat, Int, IntOrder, Frac, Algebra, Eq

import Frac
import Algebra
import Eq

-- =====================================================================
-- 1. Define equation coefficients
-- =====================================================================
def a := nat_to_frac 1      -- a = 1
def b := int_to_frac (negSucc 1)  -- b = -2
def c := int_to_frac (negSucc 2)  -- c = -3

-- =====================================================================
-- 2. Verify the original equation holds at x=3 and x=-1
-- =====================================================================

-- Verify x = 3: 1*3^2 + (-2)*3 + (-3) = 9 - 6 - 3 = 0
solve verify_x3 : Eq Frac (frac_add (frac_add (frac_mul a (square (nat_to_frac 3))) (frac_mul b (nat_to_frac 3))) c) (nat_to_frac 0) := refl Frac (nat_to_frac 0)

-- Verify x = -1: 1*(-1)^2 + (-2)*(-1) + (-3) = 1 + 2 - 3 = 0
solve verify_x_neg1 : Eq Frac (frac_add (frac_add (frac_mul a (square (frac_neg (nat_to_frac 1)))) (frac_mul b (frac_neg (nat_to_frac 1)))) c) (nat_to_frac 0) := refl Frac (nat_to_frac 0)

-- =====================================================================
-- 3. Completing the square derivation steps
-- =====================================================================

-- Step 1: Divide both sides by a (here a=1, unchanged)
-- x^2 - 2x - 3 = 0

-- Step 2: Move constant term to the right
-- x^2 - 2x = 3
-- Verify: x^2 + (-2)x = 3
solve step2 : Eq Frac (frac_add (square (nat_to_frac 3)) (frac_mul b (nat_to_frac 3))) (nat_to_frac 3) := refl Frac (nat_to_frac 3)

-- Step 3: Calculate completing-the-square constant (b/2a)^2
-- b/2a = -2/2 = -1
-- (b/2a)^2 = (-1)^2 = 1

-- Define half coefficient: b / (2a) = -2 / 2 = -1
def half_b_over_a := frac_div b (frac_mul (nat_to_frac 2) a)

-- Verify half coefficient equals -1
def step3_half : Eq Frac half_b_over_a (frac_neg (nat_to_frac 1)) := refl Frac (frac_neg (nat_to_frac 1))

-- Define completing-the-square constant
def complete_sq_term := square half_b_over_a

-- Verify completing-the-square constant equals 1
def step3_term : Eq Frac complete_sq_term (nat_to_frac 1) := refl Frac (nat_to_frac 1)

-- Step 4: Add completing-the-square constant to both sides
-- x^2 - 2x + 1 = 3 + 1 = 4
-- Verify: left side at x=3: 9 - 6 + 1 = 4
def step4_left : Eq Frac (frac_add (frac_add (square (nat_to_frac 3)) (frac_mul b (nat_to_frac 3))) complete_sq_term) (nat_to_frac 4) := refl Frac (nat_to_frac 4)

-- Step 5: Write left side as perfect square
-- (x + b/2a)^2 = (x - 1)^2
-- Verify: (3 - 1)^2 = 4
def step5_sq : Eq Frac (square (frac_add (nat_to_frac 3) half_b_over_a)) (nat_to_frac 4) := refl Frac (nat_to_frac 4)

-- =====================================================================
-- 4. Discriminant and quadratic formula
-- =====================================================================

-- Discriminant D = b^2 - 4ac = 4 - 4(1)(-3) = 4 + 12 = 16
def disc := frac_sub (square b) (frac_mul (nat_to_frac 4) (frac_mul a c))

-- Verify discriminant equals 16
solve verify_disc : Eq Frac disc (nat_to_frac 16) := refl Frac (nat_to_frac 16)

-- Quadratic formula: x = (-b +/- sqrt(D)) / 2a
-- Define sqrt(D) = 4 (here D=16 is a perfect square)
def sqrt_disc := nat_to_frac 4

-- Positive root: x1 = (-b + sqrt(D)) / 2a = (2 + 4) / 2 = 3
def root_pos := frac_div (frac_add (frac_neg b) sqrt_disc) (frac_mul (nat_to_frac 2) a)

-- Verify positive root equals 3
def verify_root_pos : Eq Frac root_pos (nat_to_frac 3) := refl Frac (nat_to_frac 3)

-- Negative root: x2 = (-b - sqrt(D)) / 2a = (2 - 4) / 2 = -1
def root_neg := frac_div (frac_sub (frac_neg b) sqrt_disc) (frac_mul (nat_to_frac 2) a)

-- Verify negative root equals -1
def verify_root_neg : Eq Frac root_neg (frac_neg (nat_to_frac 1)) := refl Frac (frac_neg (nat_to_frac 1))

-- =====================================================================
-- 5. Final verification: both roots satisfy the original equation
-- =====================================================================

-- Positive root verification: a*x1^2 + b*x1 + c = 0
def final_verify_pos : Eq Frac (frac_add (frac_add (frac_mul a (square root_pos)) (frac_mul b root_pos)) c) (nat_to_frac 0) := refl Frac (nat_to_frac 0)

-- Negative root verification: a*x2^2 + b*x2 + c = 0
def final_verify_neg : Eq Frac (frac_add (frac_add (frac_mul a (square root_neg)) (frac_mul b root_neg)) c) (nat_to_frac 0) := refl Frac (nat_to_frac 0)
