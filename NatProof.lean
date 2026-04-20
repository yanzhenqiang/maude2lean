-- 自然数运算引理
-- 依赖: Nat.lean, Eq.lean

-- n + 0 = n
theorem nat_add_zero_right : forall (n : Nat), Eq Nat (nat_add n zero) n :=
  fun n : Nat =>
    rec.Nat (fun x : Nat => Eq Nat (nat_add x zero) x)
      (refl Nat (nat_add zero zero))
      (fun n' : Nat => fun ih : Eq Nat (nat_add n' zero) n' =>
        eq_subst Nat (nat_add n' zero) n' (fun y : Nat => Eq Nat (succ (nat_add n' zero)) (succ y)) ih (refl Nat (succ (nat_add n' zero))))
      n

-- n + succ(m) = succ(n + m)
theorem nat_add_succ_right : forall (n : Nat) (m : Nat), Eq Nat (nat_add n (succ m)) (succ (nat_add n m)) :=
  fun n : Nat => fun m : Nat =>
    rec.Nat (fun x : Nat => Eq Nat (nat_add x (succ m)) (succ (nat_add x m)))
      (refl Nat (succ m))
      (fun n' : Nat => fun ih : Eq Nat (nat_add n' (succ m)) (succ (nat_add n' m)) =>
        eq_subst Nat (nat_add n' (succ m)) (succ (nat_add n' m))
          (fun y : Nat => Eq Nat (succ (nat_add n' (succ m))) (succ y))
          ih
          (refl Nat (succ (nat_add n' (succ m)))))
      n

-- m + n = n + m
theorem nat_add_comm : forall (m : Nat) (n : Nat), Eq Nat (nat_add m n) (nat_add n m) :=
  fun m : Nat => fun n : Nat =>
    rec.Nat (fun x : Nat => Eq Nat (nat_add x n) (nat_add n x))
      (nat_add_zero_right n)
      (fun m' : Nat => fun ih : Eq Nat (nat_add m' n) (nat_add n m') =>
        eq_subst Nat (nat_add m' n) (nat_add n m')
          (fun y : Nat => Eq Nat (succ (nat_add m' n)) (nat_add n (succ m')))
          ih
          (eq_subst Nat (nat_add n m') (succ (nat_add n m'))
            (fun y : Nat => Eq Nat (succ (nat_add m' n)) (succ y))
            (nat_add_succ_right n m')
            (refl Nat (succ (nat_add m' n)))))
      m
