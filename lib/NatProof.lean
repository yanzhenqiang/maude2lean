-- Natural number arithmetic lemmas
-- Dependencies: Nat.lean, Eq.lean

import Nat
import Eq
import Order

-- n + 0 = n
theorem nat_add_zero_right : forall (n : Nat), Eq Nat (nat_add n zero) n :=
  fun n : Nat =>
    rec.Nat (fun x : Nat => Eq Nat (nat_add x zero) x)
      (refl Nat zero)
      (fun n' : Nat => fun ih : Eq Nat (nat_add n' zero) n' =>
        calc (Nat)
          succ (nat_add n' zero) = succ n' :=
            eq_subst Nat (nat_add n' zero) n'
              (\y : Nat . Eq Nat (succ (nat_add n' zero)) (succ y))
              ih
              (refl Nat (succ (nat_add n' zero))))
      n

-- n + succ(m) = succ(n + m)
theorem nat_add_succ_right : forall (n : Nat) (m : Nat), Eq Nat (nat_add n (succ m)) (succ (nat_add n m)) :=
  fun n : Nat => fun m : Nat =>
    rec.Nat (fun x : Nat => Eq Nat (nat_add x (succ m)) (succ (nat_add x m)))
      (refl Nat (succ m))
      (fun n' : Nat => fun ih : Eq Nat (nat_add n' (succ m)) (succ (nat_add n' m)) =>
        calc (Nat)
          succ (nat_add n' (succ m)) = succ (succ (nat_add n' m)) :=
            eq_subst Nat (nat_add n' (succ m)) (succ (nat_add n' m))
              (\y : Nat . Eq Nat (succ (nat_add n' (succ m))) (succ y))
              ih
              (refl Nat (succ (nat_add n' (succ m)))))
      n

-- m + n = n + m
theorem nat_add_comm : forall (m : Nat) (n : Nat), Eq Nat (nat_add m n) (nat_add n m) :=
  fun m : Nat => fun n : Nat =>
    rec.Nat (fun x : Nat => Eq Nat (nat_add x n) (nat_add n x))
      (eq_sym Nat (nat_add n zero) n (nat_add_zero_right n))
      (fun m' : Nat => fun ih : Eq Nat (nat_add m' n) (nat_add n m') =>
        calc (Nat)
          succ (nat_add m' n) = succ (nat_add n m') :=
            eq_subst Nat (nat_add m' n) (nat_add n m')
              (\y : Nat . Eq Nat (succ (nat_add m' n)) (succ y))
              ih
              (refl Nat (succ (nat_add m' n)))
          _ = nat_add n (succ m') := eq_sym Nat (nat_add n (succ m')) (succ (nat_add n m')) (nat_add_succ_right n m'))
      m

-- le n n (reflexivity)
theorem le_refl : forall (n : Nat), le n n :=
  fun n : Nat =>
    rec.Nat (fun x : Nat => le x x)
      (le_zero zero)
      (fun n' : Nat => fun ih : le n' n' => le_succ n' n' ih)
      n

-- gt (succ n) n
theorem gt_succ : forall (n : Nat), gt (succ n) n :=
  fun n : Nat => le_succ n n (le_refl n)

-- (a + b) + c = a + (b + c)
theorem nat_add_assoc : forall (a : Nat) (b : Nat) (c : Nat),
  Eq Nat (nat_add (nat_add a b) c) (nat_add a (nat_add b c)) :=
  fun a : Nat => fun b : Nat => fun c : Nat =>
    rec.Nat (fun x : Nat => Eq Nat (nat_add (nat_add x b) c) (nat_add x (nat_add b c)))
      (refl Nat (nat_add b c))
      (fun a' : Nat => fun ih : Eq Nat (nat_add (nat_add a' b) c) (nat_add a' (nat_add b c)) =>
        calc (Nat)
          succ (nat_add (nat_add a' b) c) = succ (nat_add a' (nat_add b c)) :=
            eq_subst Nat (nat_add (nat_add a' b) c) (nat_add a' (nat_add b c))
              (\y : Nat . Eq Nat (succ (nat_add (nat_add a' b) c)) (succ y))
              ih
              (refl Nat (succ (nat_add (nat_add a' b) c)))
          _ = nat_add (succ a') (nat_add b c) := refl Nat (succ (nat_add a' (nat_add b c))))
      a

-- m * 0 = 0
theorem nat_mul_zero_right : forall (m : Nat), Eq Nat (nat_mul m zero) zero :=
  fun m : Nat =>
    rec.Nat (fun x : Nat => Eq Nat (nat_mul x zero) zero)
      (refl Nat zero)
      (fun m' : Nat => fun ih : Eq Nat (nat_mul m' zero) zero =>
        calc (Nat)
          nat_add (nat_mul m' zero) zero = nat_mul m' zero := nat_add_zero_right (nat_mul m' zero)
          _ = zero := ih)
      m

-- m * succ(n) = m + m * n
theorem nat_mul_succ_right : forall (m : Nat) (n : Nat),
  Eq Nat (nat_mul m (succ n)) (nat_add m (nat_mul m n)) :=
  fun m : Nat => fun n : Nat =>
    rec.Nat (fun x : Nat => Eq Nat (nat_mul x (succ n)) (nat_add x (nat_mul x n)))
      (refl Nat zero)
      (fun m' : Nat => fun ih : Eq Nat (nat_mul m' (succ n)) (nat_add m' (nat_mul m' n)) =>
        eq_subst Nat (nat_add m' (nat_mul m' n)) (nat_mul m' (succ n))
          (fun y : Nat => Eq Nat (nat_add y (succ n)) (succ (nat_add m' (nat_add (nat_mul m' n) n))))
          (eq_sym Nat (nat_mul m' (succ n)) (nat_add m' (nat_mul m' n)) ih)
          (eq_subst Nat (succ (nat_add (nat_add m' (nat_mul m' n)) n)) (succ (nat_add m' (nat_add (nat_mul m' n) n)))
            (fun y : Nat => Eq Nat (nat_add (nat_add m' (nat_mul m' n)) (succ n)) y)
            (eq_subst Nat (nat_add (nat_add m' (nat_mul m' n)) n) (nat_add m' (nat_add (nat_mul m' n) n))
              (fun y : Nat => Eq Nat (succ (nat_add (nat_add m' (nat_mul m' n)) n)) (succ y))
              (nat_add_assoc m' (nat_mul m' n) n)
              (refl Nat (succ (nat_add (nat_add m' (nat_mul m' n)) n))))
            (nat_add_succ_right (nat_add m' (nat_mul m' n)) n)))
      m

-- m * n = n * m
theorem nat_mul_comm : forall (m : Nat) (n : Nat), Eq Nat (nat_mul m n) (nat_mul n m) :=
  fun m : Nat => fun n : Nat =>
    rec.Nat (fun x : Nat => Eq Nat (nat_mul x n) (nat_mul n x))
      (eq_sym Nat (nat_mul n zero) zero (nat_mul_zero_right n))
      (fun m' : Nat => fun ih : Eq Nat (nat_mul m' n) (nat_mul n m') =>
        calc (Nat)
          nat_mul (succ m') n = nat_add (nat_mul m' n) n := refl Nat (nat_add (nat_mul m' n) n)
          _ = nat_add n (nat_mul n m') :=
            eq_subst Nat (nat_add n (nat_mul m' n)) (nat_add n (nat_mul n m'))
              (fun y : Nat => Eq Nat (nat_add (nat_mul m' n) n) y)
              (eq_subst Nat (nat_mul m' n) (nat_mul n m')
                (fun y : Nat => Eq Nat (nat_add n (nat_mul m' n)) (nat_add n y))
                ih
                (refl Nat (nat_add n (nat_mul m' n))))
              (nat_add_comm (nat_mul m' n) n)
          _ = nat_mul n (succ m') := eq_sym Nat (nat_mul n (succ m')) (nat_add n (nat_mul n m')) (nat_mul_succ_right n m'))
      m

-- le 1 (succ (nat_sub m 0))
theorem le_one_succ_sub_zero : forall (m : Nat), le (succ zero) (succ (nat_sub m zero)) :=
  fun m : Nat =>
    rec.Nat (fun x : Nat => le (succ zero) (succ (nat_sub x zero)))
      (le_refl (succ zero))
      (fun m' : Nat => fun ih : le (succ zero) (succ (nat_sub m' zero)) =>
        le_succ zero (succ m') (le_zero (succ m')))
      m

-- le 1 (succ (nat_sub m 1))
theorem le_one_succ_sub_one : forall (m : Nat), le (succ zero) (succ (nat_sub m (succ zero))) :=
  fun m : Nat =>
    rec.Nat (fun x : Nat => le (succ zero) (succ (nat_sub x (succ zero))))
      (le_refl (succ zero))
      (fun m' : Nat => fun ih : le (succ zero) (succ (nat_sub m' (succ zero))) =>
        le_one_succ_sub_zero m')
      m
