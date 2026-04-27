-- =====================================================================
-- Solve and theorem examples: basic tactics, derivations, algebra
-- Dependencies: Nat, Eq, Frac, Algebra, FracArith
-- =====================================================================

import Nat
import Eq
import Frac
import Algebra
import FracArith

-- =====================================================================
-- 1. Basic solve declarations and by-tactic tests
-- =====================================================================

solve test_solve : Nat := ?x

solve test_add : Nat := add ?x zero

solve test_eq : Eq Nat ?x zero := refl Nat zero

solve test_refl : Eq Nat zero zero := by refl

solve test_exact : Eq Nat zero zero := by exact refl Nat zero

solve test_intro : forall (n : Nat), Eq Nat n n := by intro n; refl

-- -----------------------------------------------------------------
-- 2. Theorem + by-tactic basics
-- -----------------------------------------------------------------

theorem test_intro_exact : forall (n : Nat), Eq Nat n n := by intro n; exact refl Nat n

theorem test_have : Eq Nat zero zero := by
  have h1 : Eq Nat zero zero := refl Nat zero
  exact h1

theorem test_refl_theorem : Eq Nat zero zero := by exact refl Nat zero

-- -----------------------------------------------------------------
-- 3. Chained derivations (multiple have steps)
-- -----------------------------------------------------------------

solve eq_chain : Eq Nat zero zero := by
  have h1 : Eq Nat zero zero := refl Nat zero
  exact h1

solve add_zero_chain : Eq Nat (add zero zero) zero := by
  have step1 : Eq Nat (add zero zero) zero := refl Nat zero
  exact step1

solve subst_chain : Eq Nat (add (add zero zero) zero) zero := by
  have h1 : Eq Nat (add zero zero) zero := refl Nat zero
  exact h1

solve long_chain : Eq Nat zero zero := by
  have lemma1 : Eq Nat zero zero := refl Nat zero
  have lemma2 : Eq Nat zero zero := lemma1
  have lemma3 : Eq Nat zero zero := lemma2
  exact lemma3

-- =====================================================================
-- 4. Theorem declarations (permanent, referenceable)
-- =====================================================================

theorem add_zero_right : forall (n : Nat), Eq Nat (add n zero) n :=
  rec.Nat (fun x : Nat => Eq Nat (add x zero) x)
    (refl Nat zero)
    (fun n' : Nat => fun ih : Eq Nat (add n' zero) n' =>
      eq_subst Nat (add n' zero) n'
        (fun y : Nat => Eq Nat (succ (add n' zero)) (succ y))
        ih
        (refl Nat (succ (add n' zero))))

-- -----------------------------------------------------------------
-- 5. Exploratory derivations referencing theorems
-- -----------------------------------------------------------------

solve step_add_zero : Eq Nat (add zero zero) zero :=
  add_zero_right zero

solve chain_double_zero : Eq Nat (add (add zero zero) zero) zero := by
  have h1 : Eq Nat (add zero zero) zero := add_zero_right zero
  have h2 : Eq Nat (add (add zero zero) zero) (add zero zero) := (
    eq_subst Nat (add zero zero) zero
      (fun y : Nat => Eq Nat (add (add zero zero) zero) (add y zero))
      h1
      (refl Nat (add (add zero zero) zero))
  )
  have h3 : Eq Nat (add zero zero) zero := add_zero_right zero
  have h4 : Eq Nat (add (add zero zero) zero) zero := (
    eq_subst Nat (add zero zero) zero
      (fun y : Nat => Eq Nat (add (add zero zero) zero) y)
      h3
      h2
  )
  exact h4

theorem add_zero_right_special : Eq Nat (add (add zero zero) zero) zero :=
  add_zero_right (add zero zero)

-- =====================================================================
-- 6. Quadratic formula derivation (example: x^2 - 2x - 3 = 0)
-- =====================================================================

def a := nat_to_frac 1
def b := int_to_frac (negSucc 1)
def c := int_to_frac (negSucc 2)

-- Verify x = 3 satisfies the equation
solve verify_x3 : Eq Frac (frac_add (frac_add (frac_mul a (square (nat_to_frac 3))) (frac_mul b (nat_to_frac 3))) c) (nat_to_frac 0) := refl Frac (nat_to_frac 0)

-- Verify x = -1 satisfies the equation
solve verify_x_neg1 : Eq Frac (frac_add (frac_add (frac_mul a (square (frac_neg (nat_to_frac 1)))) (frac_mul b (frac_neg (nat_to_frac 1)))) c) (nat_to_frac 0) := refl Frac (nat_to_frac 0)

-- Step 2: x^2 - 2x = 3 at x = 3
solve step2 : Eq Frac (frac_add (square (nat_to_frac 3)) (frac_mul b (nat_to_frac 3))) (nat_to_frac 3) := refl Frac (nat_to_frac 3)

-- Step 3: half coefficient b/(2a) = -1
def half_b_over_a := frac_div b (frac_mul (nat_to_frac 2) a)
def step3_half : Eq Frac half_b_over_a (frac_neg (nat_to_frac 1)) := refl Frac (frac_neg (nat_to_frac 1))

-- Completing-the-square constant = 1
def complete_sq_term := square half_b_over_a
def step3_term : Eq Frac complete_sq_term (nat_to_frac 1) := refl Frac (nat_to_frac 1)

-- Step 4: left side = 4 at x = 3
solve step4_left : Eq Frac (frac_add (frac_add (square (nat_to_frac 3)) (frac_mul b (nat_to_frac 3))) complete_sq_term) (nat_to_frac 4) := refl Frac (nat_to_frac 4)

-- Step 5: perfect square (x + b/2a)^2 = 4 at x = 3
solve step5_sq : Eq Frac (square (frac_add (nat_to_frac 3) half_b_over_a)) (nat_to_frac 4) := refl Frac (nat_to_frac 4)

-- Discriminant D = b^2 - 4ac = 16
def disc := frac_sub (square b) (frac_mul (nat_to_frac 4) (frac_mul a c))
solve verify_disc : Eq Frac disc (nat_to_frac 16) := refl Frac (nat_to_frac 16)

-- Roots via quadratic formula
def sqrt_disc := nat_to_frac 4
def root_pos := frac_div (frac_add (frac_neg b) sqrt_disc) (frac_mul (nat_to_frac 2) a)
def root_neg := frac_div (frac_sub (frac_neg b) sqrt_disc) (frac_mul (nat_to_frac 2) a)

solve verify_root_pos : Eq Frac root_pos (nat_to_frac 3) := refl Frac (nat_to_frac 3)
solve verify_root_neg : Eq Frac root_neg (frac_neg (nat_to_frac 1)) := refl Frac (frac_neg (nat_to_frac 1))

-- Final verification: both roots satisfy the original equation
def final_verify_pos : Eq Frac (frac_add (frac_add (frac_mul a (square root_pos)) (frac_mul b root_pos)) c) (nat_to_frac 0) := refl Frac (nat_to_frac 0)
def final_verify_neg : Eq Frac (frac_add (frac_add (frac_mul a (square root_neg)) (frac_mul b root_neg)) c) (nat_to_frac 0) := refl Frac (nat_to_frac 0)

-- =====================================================================
-- 7. Fraction algebra derivation chains
-- =====================================================================

axiom frac_add_comm : forall (x : Frac) (y : Frac), Eq Frac (frac_add x y) (frac_add y x)
axiom frac_add_assoc : forall (x : Frac) (y : Frac) (z : Frac), Eq Frac (frac_add (frac_add x y) z) (frac_add x (frac_add y z))

def eq_trans (A : Type) (a : A) (b : A) (c : A) (h1 : Eq A a b) (h2 : Eq A b c) : Eq A a c :=
  eq_subst A b c (fun x : A => Eq A a x) h2 h1

-- Example 1: multiplication reordering (a * b) * c = c * (b * a)
solve mul_reorder : forall (a : Frac) (b : Frac) (c : Frac),
  Eq Frac (frac_mul (frac_mul a b) c) (frac_mul c (frac_mul b a))
  := by
  intro a; intro b; intro c
  have step1 : Eq Frac (frac_mul a b) (frac_mul b a) := frac_mul_comm a b
  have step2 : Eq Frac (frac_mul (frac_mul a b) c) (frac_mul (frac_mul b a) c) := (
    eq_subst Frac (frac_mul a b) (frac_mul b a)
      (fun y : Frac => Eq Frac (frac_mul (frac_mul a b) c) (frac_mul y c))
      step1
      (refl Frac (frac_mul (frac_mul a b) c))
  )
  have step3 : Eq Frac (frac_mul (frac_mul b a) c) (frac_mul c (frac_mul b a)) := frac_mul_comm (frac_mul b a) c
  have step4 : Eq Frac (frac_mul (frac_mul a b) c) (frac_mul c (frac_mul b a)) := eq_trans Frac (frac_mul (frac_mul a b) c) (frac_mul (frac_mul b a) c) (frac_mul c (frac_mul b a)) step2 step3
  exact step4

-- Example 2: addition reordering a + (b + c) = c + (b + a)
solve add_reorder : forall (a : Frac) (b : Frac) (c : Frac),
  Eq Frac (frac_add a (frac_add b c)) (frac_add c (frac_add b a))
  := by
  intro a; intro b; intro c
  have step1 : Eq Frac (frac_add b c) (frac_add c b) := frac_add_comm b c
  have step2 : Eq Frac (frac_add a (frac_add b c)) (frac_add a (frac_add c b)) := (
    eq_subst Frac (frac_add b c) (frac_add c b)
      (fun y : Frac => Eq Frac (frac_add a (frac_add b c)) (frac_add a y))
      step1
      (refl Frac (frac_add a (frac_add b c)))
  )
  have step3 : Eq Frac (frac_add a (frac_add c b)) (frac_add (frac_add a c) b) := eq_sym Frac (frac_add (frac_add a c) b) (frac_add a (frac_add c b)) (frac_add_assoc a c b)
  have step4 : Eq Frac (frac_add a c) (frac_add c a) := frac_add_comm a c
  have step5 : Eq Frac (frac_add (frac_add a c) b) (frac_add (frac_add c a) b) := (
    eq_subst Frac (frac_add a c) (frac_add c a)
      (fun y : Frac => Eq Frac (frac_add (frac_add a c) b) (frac_add y b))
      step4
      (refl Frac (frac_add (frac_add a c) b))
  )
  have step6 : Eq Frac (frac_add (frac_add c a) b) (frac_add c (frac_add a b)) := frac_add_assoc c a b
  have step7 : Eq Frac (frac_add a b) (frac_add b a) := frac_add_comm a b
  have step8 : Eq Frac (frac_add c (frac_add a b)) (frac_add c (frac_add b a)) := (
    eq_subst Frac (frac_add a b) (frac_add b a)
      (fun y : Frac => Eq Frac (frac_add c (frac_add a b)) (frac_add c y))
      step7
      (refl Frac (frac_add c (frac_add a b)))
  )
  have chain1 : Eq Frac (frac_add a (frac_add b c)) (frac_add (frac_add a c) b) := (
    eq_trans Frac (frac_add a (frac_add b c)) (frac_add a (frac_add c b)) (frac_add (frac_add a c) b) step2 step3
  )
  have chain2 : Eq Frac (frac_add a (frac_add b c)) (frac_add (frac_add c a) b) := (
    eq_trans Frac (frac_add a (frac_add b c)) (frac_add (frac_add a c) b) (frac_add (frac_add c a) b) chain1 step5
  )
  have chain3 : Eq Frac (frac_add a (frac_add b c)) (frac_add c (frac_add a b)) := (
    eq_trans Frac (frac_add a (frac_add b c)) (frac_add (frac_add c a) b) (frac_add c (frac_add a b)) chain2 step6
  )
  have chain4 : Eq Frac (frac_add a (frac_add b c)) (frac_add c (frac_add b a)) := (
    eq_trans Frac (frac_add a (frac_add b c)) (frac_add c (frac_add a b)) (frac_add c (frac_add b a)) chain3 step8
  )
  exact chain4

-- Example 3: completing-the-square conceptual framework
axiom frac_dist_left : forall (a : Frac) (b : Frac) (c : Frac),
  Eq Frac (frac_mul a (frac_add b c)) (frac_add (frac_mul a b) (frac_mul a c))

solve complete_square_demo : Eq Frac
  (frac_add (frac_sub (square (nat_to_frac 3)) (frac_mul (nat_to_frac 2) (nat_to_frac 3))) (nat_to_frac 1))
  (square (frac_add (nat_to_frac 3) (int_to_frac (negSucc 0))))
  := by
  exact refl Frac (frac_add (frac_sub (square (nat_to_frac 3)) (frac_mul (nat_to_frac 2) (nat_to_frac 3))) (nat_to_frac 1))
