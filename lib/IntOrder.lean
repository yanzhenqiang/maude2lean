-- Int ordering, absolute value, subtraction
-- Dependencies: Order.lean (le), True.lean (True, False)

import Nat
import Order
import logic
import Int

-- Int successor (using recursor to avoid nested match)
def int_succ (a : Int) : Int :=
  rec.Int (fun _ => Int) (fun n => ofNat (succ n)) (fun n => ofNat zero) a

-- Int predecessor
def int_pred (a : Int) : Int :=
  rec.Int (fun _ => Int) (fun n =>
    match n : Nat with
    | zero => negSucc zero
    | succ n' => ofNat n'
  ) (fun n => negSucc (succ n)) a

-- Int negation
def int_neg (a : Int) : Int :=
  rec.Int (fun _ => Int)
    (fun n =>
      match n : Nat with
      | zero => ofNat zero
      | succ n' => negSucc n'
    )
    (fun n => ofNat (succ n))
    a

-- Int ordering
-- ofNat m >= 0, negSucc m < 0
def int_le (a : Int) (b : Int) : Prop :=
  rec.Int (fun _ => Int -> Prop)
    (fun m => rec.Int (fun _ => Prop)
      (fun n => le m n)
      (fun n => False)
      b)
    (fun m => rec.Int (fun _ => Prop)
      (fun n => True)
      (fun n => le n m)
      b)
    a

-- Strict less-than: a < b = succ(a) <= b
def int_lt (a : Int) (b : Int) : Prop := int_le (int_succ a) b

-- Greater-than-or-equal, greater-than
def int_ge (a : Int) (b : Int) : Prop := int_le b a
def int_gt (a : Int) (b : Int) : Prop := int_lt b a

-- Int absolute value
def int_abs (a : Int) : Int :=
  rec.Int (fun _ => Int)
    (fun n => ofNat n)
    (fun n => ofNat (succ n))
    a

-- Int subtraction: a - b = a + (-b)
def int_sub (a : Int) (b : Int) : Int := int_add a (int_neg b)
