import Nat

inductive Int where
| ofNat : Nat -> Int
| negSucc : Nat -> Int

def int_add (a : Int) (b : Int) : Int :=
  rec.Int (fun _ => Int)
    (fun m : Nat => rec.Int (fun _ => Int)
      (fun n : Nat => ofNat (nat_add m n))
      (fun n : Nat => rec.Nat (fun _ => Nat -> Int)
        (fun n => negSucc n)
        (fun m' : Nat => fun ih : Nat -> Int => fun n : Nat =>
          rec.Nat (fun _ => Int) (ofNat m')
            (fun n' : Nat => fun _ : Int => ih n')
            n)
        m
        n)
      b)
    (fun m : Nat => rec.Int (fun _ => Int)
      (fun n : Nat => rec.Nat (fun _ => Nat -> Int)
        (fun n => rec.Nat (fun _ => Int)
          (negSucc 0)
          (fun n' : Nat => fun _ : Int => ofNat n')
          n)
        (fun m' : Nat => fun ih : Nat -> Int => fun n : Nat =>
          rec.Nat (fun _ => Int) (negSucc (succ m'))
            (fun n' : Nat => fun _ : Int => ih n')
            n)
        m
        n)
      (fun n : Nat => negSucc (nat_add m (succ n)))
      b)
    a

def int_mul (a : Int) (b : Int) : Int :=
  rec.Int (fun _ => Int)
    (fun m : Nat => rec.Int (fun _ => Int)
      (fun n : Nat => ofNat (nat_mul m n))
      (fun n : Nat => rec.Nat (fun _ => Int) (ofNat 0)
        (fun m' : Nat => fun _ : Int => negSucc (nat_add (nat_mul m' (succ n)) n))
        m)
      b)
    (fun m : Nat => rec.Int (fun _ => Int)
      (fun n : Nat => rec.Nat (fun _ => Int) (ofNat 0)
        (fun n' : Nat => fun _ : Int => negSucc (nat_add (nat_mul n' (succ m)) m))
        n)
      (fun n : Nat => ofNat (nat_mul (succ m) (succ n)))
      b)
    a
