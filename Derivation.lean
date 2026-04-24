-- =====================================================================
-- 多步推导示例：theorem 与 solve 分离
-- theorem = 永久声明，可被引用
-- solve   = 一次性推导验证，不注册
-- =====================================================================

-- 依赖: Nat, Eq

-- -----------------------------------------------------------------
-- 1. 基础定理（永久声明，后续可引用）
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
-- 2. 探索性推导（solve）—— 多步 tactic，一次性验证
-- -----------------------------------------------------------------

-- 直接引用定理的 solve（无 ?x，纯验证）
solve step_add_zero : Eq Nat (add zero zero) zero :=
  add_zero_right zero

-- 多步 by-tactic 的 solve（无 ?x，纯演绎验证）
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
-- 3. 另一个 theorem（不引用 solve，只引用 theorem）
-- -----------------------------------------------------------------

theorem add_zero_right_special : Eq Nat (add (add zero zero) zero) zero :=
  add_zero_right (add zero zero)
