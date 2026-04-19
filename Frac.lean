-- 分数类型 Frac = Int / (Nat+1)
-- 用 (num : Int, den : Nat) 表示 num/(den+1)，分母恒正

inductive Frac where
| mk : Int -> Nat -> Frac

-- 投影
def frac_num (f : Frac) : Int :=
  match f : Frac with
  | mk n d => n

def frac_den (f : Frac) : Nat :=
  match f : Frac with
  | mk n d => d

-- 实际分母 = den + 1
def frac_den1 (f : Frac) : Nat := succ (frac_den f)

-- 构造子
def int_to_frac (n : Int) : Frac := mk n zero
def nat_to_frac (n : Nat) : Frac := mk (ofNat n) zero

-- 分数加法: n1/d1 + n2/d2 = (n1*d2 + n2*d1) / (d1*d2)
def frac_add (f1 : Frac) (f2 : Frac) : Frac :=
  mk (int_add (int_mul (frac_num f1) (ofNat (frac_den1 f2)))
              (int_mul (frac_num f2) (ofNat (frac_den1 f1))))
     (nat_mul (frac_den1 f1) (frac_den1 f2))

-- 分数减法
def frac_sub (f1 : Frac) (f2 : Frac) : Frac :=
  mk (int_sub (int_mul (frac_num f1) (ofNat (frac_den1 f2)))
              (int_mul (frac_num f2) (ofNat (frac_den1 f1))))
     (nat_mul (frac_den1 f1) (frac_den1 f2))

-- 分数乘法
def frac_mul (f1 : Frac) (f2 : Frac) : Frac :=
  mk (int_mul (frac_num f1) (frac_num f2))
     (nat_mul (frac_den1 f1) (frac_den1 f2))

-- 分数绝对值
def frac_abs (f : Frac) : Frac :=
  mk (int_abs (frac_num f)) (frac_den f)

-- 分数小于: n1/d1 < n2/d2  iff  n1*d2 < n2*d1
def frac_lt (f1 : Frac) (f2 : Frac) : Prop :=
  int_lt (int_mul (frac_num f1) (ofNat (frac_den1 f2)))
         (int_mul (frac_num f2) (ofNat (frac_den1 f1)))

-- 1/(k+1)
def frac_inv (k : Nat) : Frac := mk (ofNat 1) k
