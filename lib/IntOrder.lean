-- Int 序关系、绝对值、减法
-- 依赖: Order.lean (le), True.lean (True, False)

import Nat
import Order
import True
import Int

-- Int 后继（用 recursor，避免嵌套 match）
def int_succ (a : Int) : Int :=
  rec.Int (fun _ => Int) (fun n => ofNat (succ n)) (fun n => ofNat zero) a

-- Int 前驱
def int_pred (a : Int) : Int :=
  rec.Int (fun _ => Int) (fun n =>
    match n : Nat with
    | zero => negSucc zero
    | succ n' => ofNat n'
  ) (fun n => negSucc (succ n)) a

-- Int 相反数
def int_neg (a : Int) : Int :=
  rec.Int (fun _ => Int)
    (fun n =>
      match n : Nat with
      | zero => ofNat zero
      | succ n' => negSucc n'
    )
    (fun n => ofNat (succ n))
    a

-- Int 序关系
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

-- 严格小于: a < b = succ(a) <= b
def int_lt (a : Int) (b : Int) : Prop := int_le (int_succ a) b

-- 大于等于、大于
def int_ge (a : Int) (b : Int) : Prop := int_le b a
def int_gt (a : Int) (b : Int) : Prop := int_lt b a

-- Int 绝对值
def int_abs (a : Int) : Int :=
  rec.Int (fun _ => Int)
    (fun n => ofNat n)
    (fun n => ofNat (succ n))
    a

-- Int 减法: a - b = a + (-b)
def int_sub (a : Int) (b : Int) : Int := int_add a (int_neg b)
