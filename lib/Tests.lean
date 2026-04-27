-- =====================================================================
-- 基础功能测试集
-- 覆盖 solve、theorem、by-tactic、have、intro、exact、refl 等
-- 依赖: Nat.lean, Eq.lean
-- =====================================================================

import Nat
import Eq

-- -----------------------------------------------------------------
-- 1. solve 声明（含 metavariable）
-- -----------------------------------------------------------------

solve test_solve : Nat := ?x

solve test_add : Nat := add ?x zero

solve test_eq : Eq Nat ?x zero := refl Nat zero

-- -----------------------------------------------------------------
-- 2. by-tactic 基础
-- -----------------------------------------------------------------

solve test_refl : Eq Nat zero zero := by refl

solve test_exact : Eq Nat zero zero := by exact refl Nat zero

solve test_intro : forall (n : Nat), Eq Nat n n := by intro n; refl

-- -----------------------------------------------------------------
-- 3. theorem + by-tactic
-- -----------------------------------------------------------------

theorem test_intro_exact : forall (n : Nat), Eq Nat n n := by intro n; exact refl Nat n

theorem test_have : Eq Nat zero zero := by
  have h1 : Eq Nat zero zero := refl Nat zero
  exact h1

theorem test_refl_theorem : Eq Nat zero zero := by exact refl Nat zero

-- -----------------------------------------------------------------
-- 4. 链式推导（单 solve 内多步 have）
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
