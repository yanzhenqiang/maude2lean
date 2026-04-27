-- =====================================================================
-- Multi-step derivation example: theorem and solve separation
-- theorem = permanent declaration, can be referenced
-- solve   = one-shot derivation check, not registered
-- =====================================================================

-- Dependencies: Nat, Eq

import Nat
import Eq

-- -----------------------------------------------------------------
-- 1. Basic theorems (permanent declarations, can be referenced later)
-- -----------------------------------------------------------------

theorem add_zero_right : forall (n : Nat), Eq Nat (add n zero) n :=
  rec.Nat (fun x : Nat => Eq Nat (add x zero) x)
    (refl Nat zero)
    (fun n' : Nat => fun ih : Eq Nat (add n' zero) n' =>
      eq_subst Nat (add n' zero) n'
        (fun y : Nat => Eq Nat (succ (add n' zero)) (succ y))
        ih
        (refl Nat (succ (add n' zero))))

-- -----------------------------------------------------------------
-- 2. Exploratory derivations (solve) -- multi-step tactic, one-shot check
-- -----------------------------------------------------------------

-- Directly reference theorem in solve (no ?x, pure verification)
solve step_add_zero : Eq Nat (add zero zero) zero :=
  add_zero_right zero

-- Multi-step by-tactic solve (no ?x, pure deductive verification)
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

-- -----------------------------------------------------------------
-- 3. Another theorem (does not reference solve, only references theorem)
-- -----------------------------------------------------------------

theorem add_zero_right_special : Eq Nat (add (add zero zero) zero) zero :=
  add_zero_right (add zero zero)
