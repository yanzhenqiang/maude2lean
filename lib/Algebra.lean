-- 代数基础扩展
-- 为求根公式推导提供必要的运算
-- 依赖: Nat, Int, IntOrder, Frac

-- 分数取负: -(n/d) = (-n)/d
def frac_neg (f : Frac) : Frac := mk (int_neg (frac_num f)) (frac_den f)

-- 分数除法: (n1/d1) / (n2/d2) = (n1*d2) / (n2*d1)
-- 简化为乘以倒数，假设除数非零
def frac_div (f1 : Frac) (f2 : Frac) : Frac :=
  mk (int_mul (frac_num f1) (ofNat (frac_den1 f2)))
     (nat_sub (nat_mul (frac_den1 f1)
       (match int_abs (frac_num f2) : Int with
        | ofNat n => n
        | negSucc n => 0))
       (succ zero))

-- 平方
def square (f : Frac) : Frac := frac_mul f f
