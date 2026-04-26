-- =====================================================================
-- 十进制整数系统（Decimal 高位在前，符合书写直觉）
-- 内部计算通过 dec_to_le / le_to_dec 反转到底层 List Digit
-- =====================================================================

-- -----------------------------------------------------------------
-- 1. 数字 0-9（10 个基本符号）
-- -----------------------------------------------------------------

inductive Digit where
| d0 : Digit
| d1 : Digit
| d2 : Digit
| d3 : Digit
| d4 : Digit
| d5 : Digit
| d6 : Digit
| d7 : Digit
| d8 : Digit
| d9 : Digit

-- -----------------------------------------------------------------
-- 2. Bool（进位标记）
-- -----------------------------------------------------------------

inductive Bool where
| false : Bool
| true : Bool

inductive Nat where
| zero : Nat
| succ : Nat -> Nat

-- -----------------------------------------------------------------
-- 3. 相等类型 Eq（带参数版本，支持 refl）
-- -----------------------------------------------------------------

inductive Eq : forall (A : Type) (a : A) (b : A), Prop where
| refl : forall (A : Type) (a : A), Eq A a a

def not (b : Bool) : Bool :=
  match b : Bool with | false => true | true => false

def is_zero (n : Nat) : Bool :=
  rec.Nat (fun _ => Bool) true (fun n' ih => false) n

def nat_gt (m n : Nat) : Bool :=
  rec.Nat (fun _ => Nat -> Bool)
    (fun n => false)
    (fun m' => \ih : Nat -> Bool . \n : Nat . rec.Nat (fun _ => Bool) true (fun n' ih2 => ih n') n)
    m
    n

def nat_eq (m n : Nat) : Bool :=
  rec.Nat (fun _ => Nat -> Bool)
    (fun n => is_zero n)
    (fun m' => \ih : Nat -> Bool . \n : Nat . rec.Nat (fun _ => Bool) false (fun n' ih2 => ih n') n)
    m
    n

-- -----------------------------------------------------------------
-- 3. 通用 List
-- -----------------------------------------------------------------

inductive List (A : Type) where
| nil : List A
| cons : A -> List A -> List A

-- -----------------------------------------------------------------
-- 4. Decimal = 高位在前的十进制数
--    0   = dnil
--    123 = D1 (D2 (D3 Dnil))
-- -----------------------------------------------------------------

inductive Decimal where
| Dnil : Decimal
| D0 : Decimal -> Decimal
| D1 : Decimal -> Decimal
| D2 : Decimal -> Decimal
| D3 : Decimal -> Decimal
| D4 : Decimal -> Decimal
| D5 : Decimal -> Decimal
| D6 : Decimal -> Decimal
| D7 : Decimal -> Decimal
| D8 : Decimal -> Decimal
| D9 : Decimal -> Decimal

-- -----------------------------------------------------------------
-- 5. Digit -> Nat 映射（验证用）
-- -----------------------------------------------------------------

def digit_to_nat (d : Digit) : Nat :=
  rec.Digit (fun _ => Nat)
    zero
    (succ zero)
    (succ (succ zero))
    (succ (succ (succ zero)))
    (succ (succ (succ (succ zero))))
    (succ (succ (succ (succ (succ zero)))))
    (succ (succ (succ (succ (succ (succ zero))))))
    (succ (succ (succ (succ (succ (succ (succ zero)))))))
    (succ (succ (succ (succ (succ (succ (succ (succ zero))))))))
    (succ (succ (succ (succ (succ (succ (succ (succ (succ zero)))))))))
    d

-- -----------------------------------------------------------------
-- 6. 转换函数：Decimal <-> List Digit（反转）
-- -----------------------------------------------------------------

def le_append_digit (n : List Digit) (d : Digit) : List Digit :=
  rec.List Digit (fun _ : List Digit => List Digit)
    (cons Digit d (nil Digit))
    (\d' : Digit . \ds : List Digit . \ih : List Digit . cons Digit d' ih)
    n

def dec_to_le (d : Decimal) : List Digit :=
  rec.Decimal (fun _ => List Digit)
    (nil Digit)
    (fun _ => \ih : List Digit . le_append_digit ih d0)
    (fun _ => \ih : List Digit . le_append_digit ih d1)
    (fun _ => \ih : List Digit . le_append_digit ih d2)
    (fun _ => \ih : List Digit . le_append_digit ih d3)
    (fun _ => \ih : List Digit . le_append_digit ih d4)
    (fun _ => \ih : List Digit . le_append_digit ih d5)
    (fun _ => \ih : List Digit . le_append_digit ih d6)
    (fun _ => \ih : List Digit . le_append_digit ih d7)
    (fun _ => \ih : List Digit . le_append_digit ih d8)
    (fun _ => \ih : List Digit . le_append_digit ih d9)
    d

-- 将 Digit 转为单个 Decimal
def digit_to_decimal (d : Digit) : Decimal :=
  match d : Decimal with
  | d0 => D0 Dnil | d1 => D1 Dnil | d2 => D2 Dnil | d3 => D3 Dnil
  | d4 => D4 Dnil | d5 => D5 Dnil | d6 => D6 Dnil | d7 => D7 Dnil
  | d8 => D8 Dnil | d9 => D9 Dnil

-- 将 Digit 追加到 Decimal 末尾（保持高位在前）
def dec_append_digit (n : Decimal) (d : Digit) : Decimal :=
  rec.Decimal (fun _ => Decimal)
    (digit_to_decimal d)
    (fun _ ih => D0 ih)
    (fun _ ih => D1 ih)
    (fun _ ih => D2 ih)
    (fun _ ih => D3 ih)
    (fun _ ih => D4 ih)
    (fun _ ih => D5 ih)
    (fun _ ih => D6 ih)
    (fun _ ih => D7 ih)
    (fun _ ih => D8 ih)
    (fun _ ih => D9 ih)
    n

def le_to_dec (n : List Digit) : Decimal :=
  rec.List Digit (fun _ => Decimal)
    Dnil
    (fun d ds ih => dec_append_digit ih d)
    n

-- -----------------------------------------------------------------
-- 7. 底层 List Digit 算法（低位在前，用于计算）
-- -----------------------------------------------------------------

def nat_add (m n : Nat) : Nat :=
  rec.Nat (fun _ => Nat) m (fun n' ih => succ ih) n

def le_to_nat (n : List Digit) : Nat :=
  rec.List Digit (fun _ => Nat)
    zero
    (fun d ds ih =>
      nat_add (digit_to_nat d) (nat_add ih (nat_add ih (nat_add ih (nat_add ih (nat_add ih (nat_add ih (nat_add ih (nat_add ih (nat_add ih ih))))))))))
    n

def le_decimal_succ (n : List Digit) : List Digit :=
  rec.List Digit (fun _ => List Digit)
    (cons Digit d1 (nil Digit))
    (fun d ds ih =>
      match d : List Digit with
      | d0 => cons Digit d1 ds
      | d1 => cons Digit d2 ds
      | d2 => cons Digit d3 ds
      | d3 => cons Digit d4 ds
      | d4 => cons Digit d5 ds
      | d5 => cons Digit d6 ds
      | d6 => cons Digit d7 ds
      | d7 => cons Digit d8 ds
      | d8 => cons Digit d9 ds
      | d9 => cons Digit d0 ih
      )
    n

def le_nat_to_dec (n : Nat) : List Digit :=
  rec.Nat (fun _ => List Digit)
    (nil Digit)
    (fun n' ih => le_decimal_succ ih)
    n

def digit_succ_mod10 (d : Digit) : Digit :=
  match d : Digit with
  | d0 => d1 | d1 => d2 | d2 => d3 | d3 => d4 | d4 => d5
  | d5 => d6 | d6 => d7 | d7 => d8 | d8 => d9 | d9 => d0

def nat_to_digit (n : Nat) : Digit :=
  rec.Nat (fun _ => Digit) d0 (fun n' ih => digit_succ_mod10 ih) n

def digit_add_result (d1 d2 : Digit) (carry : Bool) : Digit :=
  nat_to_digit (nat_add (nat_add (digit_to_nat d1) (digit_to_nat d2))
    (match carry : Nat with | false => zero | true => succ zero))

def digit_add_carry (d1 d2 : Digit) (carry : Bool) : Bool :=
  nat_gt (nat_add (nat_add (digit_to_nat d1) (digit_to_nat d2))
    (match carry : Nat with | false => zero | true => succ zero))
    (succ (succ (succ (succ (succ (succ (succ (succ (succ zero)))))))))

def digit_eq (d1 d2 : Digit) : Bool :=
  nat_eq (digit_to_nat d1) (digit_to_nat d2)

def le_add (a b : List Digit) : List Digit :=
  rec.List Digit (fun _ => List Digit -> Bool -> List Digit)
    (fun b carry =>
      rec.List Digit (fun _ => Bool -> List Digit)
        (fun carry => match carry : List Digit with | false => nil Digit | true => cons Digit d1 (nil Digit))
        (fun db b' ih carry =>
          cons Digit (digit_add_result db d0 carry) (ih (digit_add_carry db d0 carry)))
        b carry)
    (fun da a' ih b carry =>
      rec.List Digit (fun _ => Bool -> List Digit)
        (fun carry =>
          cons Digit (digit_add_result da d0 carry) (ih (nil Digit) (digit_add_carry da d0 carry)))
        (fun db b' ih2 carry =>
          cons Digit (digit_add_result da db carry) (ih b' (digit_add_carry da db carry)))
        b carry)
    a b false

def le_eq (a b : List Digit) : Bool :=
  rec.List Digit (fun _ => List Digit -> Bool)
    (fun b => rec.List Digit (fun _ => Bool) true (fun db b' ih => false) b)
    (fun da a' ih b =>
      rec.List Digit (fun _ => Bool) false
        (fun db b' ih2 => match digit_eq da db : Bool with | false => false | true => ih b') b)
    a b

-- -----------------------------------------------------------------
-- 8. Decimal API（wrapper，用户可见）
-- -----------------------------------------------------------------

def dec_to_nat (n : Decimal) : Nat := le_to_nat (dec_to_le n)
def nat_to_dec (n : Nat) : Decimal := le_to_dec (le_nat_to_dec n)
def decimal_succ (n : Decimal) : Decimal := le_to_dec (le_decimal_succ (dec_to_le n))
def dec_add (a b : Decimal) : Decimal := le_to_dec (le_add (dec_to_le a) (dec_to_le b))
def dec_eq (a b : Decimal) : Bool := le_eq (dec_to_le a) (dec_to_le b)

def nat_pred (n : Nat) : Nat :=
  rec.Nat (fun _ => Nat) zero (fun n' ih => n') n

def nat_sub (m n : Nat) : Nat :=
  rec.Nat (fun _ => Nat) m (fun n' ih => nat_pred ih) n

def nat_mul (m n : Nat) : Nat :=
  rec.Nat (fun _ => Nat) zero (fun n' ih => nat_add m ih) n

def nat_div_fuel (fuel : Nat) (m n : Nat) : Nat :=
  rec.Nat (fun _ => Nat -> Nat -> Nat)
    (fun m n => zero)
    (fun fuel' ih => fun m n =>
      match nat_gt n zero : Nat with
      | false => zero
      | true => match nat_gt m n : Nat with
        | false => match nat_eq m n : Nat with
          | true => succ zero
          | false => zero
        | true => succ (ih (nat_sub m n) n))
    fuel
    m
    n

def nat_div (m n : Nat) : Nat := nat_div_fuel m m n

def nat_mod (m n : Nat) : Nat := nat_sub m (nat_mul n (nat_div m n))

def dec_sub (a b : Decimal) : Decimal := nat_to_dec (nat_sub (dec_to_nat a) (dec_to_nat b))
def dec_mul (a b : Decimal) : Decimal := nat_to_dec (nat_mul (dec_to_nat a) (dec_to_nat b))
def dec_div (a b : Decimal) : Decimal := nat_to_dec (nat_div (dec_to_nat a) (dec_to_nat b))
def dec_mod (a b : Decimal) : Decimal := nat_to_dec (nat_mod (dec_to_nat a) (dec_to_nat b))
def dec_lt (a b : Decimal) : Bool := nat_gt (dec_to_nat b) (dec_to_nat a)

-- -----------------------------------------------------------------
-- 9. Digit x Decimal 乘法
-- -----------------------------------------------------------------

-- Digit x Decimal 乘法（通过 Nat 中转）
def digit_decimal_mul (d : Digit) (n : Decimal) : Decimal :=
  nat_to_dec (nat_mul (digit_to_nat d) (dec_to_nat n))

-- -----------------------------------------------------------------
-- 10. 带符号十进制整数
-- -----------------------------------------------------------------

inductive Sign where
| pos : Sign
| neg : Sign

inductive SignedDecimal where
| mk : Sign -> Decimal -> SignedDecimal

def sd_neg (sd : SignedDecimal) : SignedDecimal :=
  match sd : SignedDecimal with
  | mk pos d => mk neg d
  | mk neg d => mk pos d

def sd_abs (sd : SignedDecimal) : Decimal :=
  match sd : Decimal with | mk _ d => d

def add_pos_neg (da db : Decimal) : SignedDecimal :=
  (match dec_lt da db : SignedDecimal with
   | true => mk neg (dec_sub db da)
   | false => mk pos (dec_sub da db))

def signed_dec_add (a b : SignedDecimal) : SignedDecimal :=
  match a : SignedDecimal with | mk sa da =>
    match b : SignedDecimal with | mk sb db =>
      rec.Sign (fun _ => SignedDecimal)
        (rec.Sign (fun _ => SignedDecimal)
          (mk pos (dec_add da db))
          (add_pos_neg da db)
          sb)
        (rec.Sign (fun _ => SignedDecimal)
          (add_pos_neg db da)
          (mk neg (dec_add da db))
          sb)
        sa

def signed_dec_sub (a b : SignedDecimal) : SignedDecimal :=
  signed_dec_add a (sd_neg b)

def signed_dec_mul (a b : SignedDecimal) : SignedDecimal :=
  match a : SignedDecimal with | mk sa da =>
    match b : SignedDecimal with | mk sb db =>
      rec.Sign (fun _ => SignedDecimal)
        (rec.Sign (fun _ => SignedDecimal)
          (mk pos (dec_mul da db))
          (mk neg (dec_mul da db))
          sb)
        (rec.Sign (fun _ => SignedDecimal)
          (mk neg (dec_mul da db))
          (mk pos (dec_mul da db))
          sb)
        sa

-- -----------------------------------------------------------------
-- 11. 定点小数
-- -----------------------------------------------------------------

inductive Prod (A : Type) (B : Type) where
| pair : A -> B -> Prod A B

def FloatDecimal := Prod Decimal Decimal

-- 拼接两个 Decimal（高位在前）
def dec_append (a b : Decimal) : Decimal :=
  rec.Decimal (fun _ => Decimal)
    b
    (fun _ ih => D0 ih)
    (fun _ ih => D1 ih)
    (fun _ ih => D2 ih)
    (fun _ ih => D3 ih)
    (fun _ ih => D4 ih)
    (fun _ ih => D5 ih)
    (fun _ ih => D6 ih)
    (fun _ ih => D7 ih)
    (fun _ ih => D8 ih)
    (fun _ ih => D9 ih)
    a

-- Decimal 位数（0 用 Dnil 表示）
def dec_len (d : Decimal) : Decimal :=
  rec.Decimal (fun _ => Decimal)
    Dnil
    (fun _ ih => decimal_succ ih)
    (fun _ ih => decimal_succ ih)
    (fun _ ih => decimal_succ ih)
    (fun _ ih => decimal_succ ih)
    (fun _ ih => decimal_succ ih)
    (fun _ ih => decimal_succ ih)
    (fun _ ih => decimal_succ ih)
    (fun _ ih => decimal_succ ih)
    (fun _ ih => decimal_succ ih)
    (fun _ ih => decimal_succ ih)
    d

-- 从整数部分和小数部分构造 FloatDecimal
-- 如 float_from_parts (D1 (D2 (D3 Dnil))) (D4 (D5 Dnil)) = 123.45
def float_from_parts (int_part : Decimal) (frac_part : Decimal) : FloatDecimal :=
  pair Decimal Decimal (dec_append int_part frac_part) (dec_len frac_part)

def float_pad (d : Decimal) (n : Decimal) : Decimal :=
  le_to_dec (rec.Nat (fun _ => List Digit) (dec_to_le d)
    (fun n' ih => cons Digit d0 ih) (dec_to_nat n))

def float_add (a b : FloatDecimal) : FloatDecimal :=
  match a : FloatDecimal with | pair Decimal Decimal da pa =>
    match b : FloatDecimal with | pair Decimal Decimal db pb =>
      (match dec_lt pa pb : FloatDecimal with
       | true => pair Decimal Decimal (dec_add (float_pad da (dec_sub pb pa)) db) pb
       | false => pair Decimal Decimal (dec_add da (float_pad db (dec_sub pa pb))) pa)

def float_sub (a b : FloatDecimal) : FloatDecimal :=
  match a : FloatDecimal with | pair Decimal Decimal da pa =>
    match b : FloatDecimal with | pair Decimal Decimal db pb =>
      (match dec_lt pa pb : FloatDecimal with
       | true => pair Decimal Decimal (dec_sub (float_pad da (dec_sub pb pa)) db) pb
       | false => pair Decimal Decimal (dec_sub da (float_pad db (dec_sub pa pb))) pa)

def float_mul (a b : FloatDecimal) : FloatDecimal :=
  match a : FloatDecimal with | pair Decimal Decimal da pa =>
    match b : FloatDecimal with | pair Decimal Decimal db pb =>
      pair Decimal Decimal (dec_mul da db) (dec_add pa pb)

-- -----------------------------------------------------------------
-- 12. 分数
-- -----------------------------------------------------------------

def RatDecimal := Prod Decimal Decimal

def rat_add (a b : RatDecimal) : RatDecimal :=
  match a : RatDecimal with | pair Decimal Decimal na da =>
    match b : RatDecimal with | pair Decimal Decimal nb db =>
      pair Decimal Decimal
        (dec_add (dec_mul na db) (dec_mul nb da))
        (dec_mul da db)

def rat_sub (a b : RatDecimal) : RatDecimal :=
  match a : RatDecimal with | pair Decimal Decimal na da =>
    match b : RatDecimal with | pair Decimal Decimal nb db =>
      pair Decimal Decimal
        (dec_sub (dec_mul na db) (dec_mul nb da))
        (dec_mul da db)

def rat_mul (a b : RatDecimal) : RatDecimal :=
  match a : RatDecimal with | pair Decimal Decimal na da =>
    match b : RatDecimal with | pair Decimal Decimal nb db =>
      pair Decimal Decimal
        (dec_mul na nb)
        (dec_mul da db)

def rat_div (a b : RatDecimal) : RatDecimal :=
  match a : RatDecimal with | pair Decimal Decimal na da =>
    match b : RatDecimal with | pair Decimal Decimal nb db =>
      pair Decimal Decimal
        (dec_mul na db)
        (dec_mul da nb)

-- -----------------------------------------------------------------
-- 13. 幂运算
-- -----------------------------------------------------------------

def nat_pow (base : Nat) (exp : Nat) : Nat :=
  rec.Nat (fun _ => Nat) (succ zero) (fun exp' ih => nat_mul base ih) exp

def dec_pow (base : Decimal) (exp : Decimal) : Decimal :=
  nat_to_dec (nat_pow (dec_to_nat base) (dec_to_nat exp))

-- -----------------------------------------------------------------
-- 14. 科学计数法
-- -----------------------------------------------------------------

def dec_ten_pow (n : Nat) : Decimal :=
  le_to_dec (rec.Nat (fun _ => List Digit) (cons Digit d1 (nil Digit))
    (fun n' ih => cons Digit d0 ih) n)

def ScientificDecimal := Prod Decimal SignedDecimal

def sci_to_decimal (sci : ScientificDecimal) : FloatDecimal :=
  match sci : FloatDecimal with | pair Decimal SignedDecimal mantissa exp_sd =>
    match exp_sd : FloatDecimal with | mk sign exp_dec =>
      rec.Sign (fun _ => FloatDecimal)
        (pair Decimal Decimal (dec_mul mantissa (dec_ten_pow (dec_to_nat exp_dec))) Dnil)
        (pair Decimal Decimal mantissa exp_dec)
        sign

-- -----------------------------------------------------------------
-- 19. 列表排序（quicksort）
-- -----------------------------------------------------------------

def list_append (A : Type) (xs ys : List A) : List A :=
  rec.List A (fun _ => List A)
    ys
    (fun x xs ih => cons A x ih)
    xs

-- 通用过滤：保留满足 p x = true 的元素
def list_filter (A : Type) (p : A -> Bool) (xs : List A) : List A :=
  rec.List A (fun _ => List A)
    (nil A)
    (fun x xs ih => match p x : List A with
      | true => cons A x ih
      | false => ih)
    xs

-- 列表最大值（空列表返回默认值）
def list_max (A : Type) (le : A -> A -> Bool) (default : A) (xs : List A) : A :=
  rec.List A (fun _ => A)
    default
    (fun x xs ih => match le x ih : A with
      | true => ih
      | false => x)
    xs

-- 列表最小值（空列表返回默认值）
def list_min (A : Type) (le : A -> A -> Bool) (default : A) (xs : List A) : A :=
  rec.List A (fun _ => A)
    default
    (fun x xs ih => match le x ih : A with
      | true => x
      | false => ih)
    xs

-- 列表长度
def list_length (A : Type) (xs : List A) : Nat :=
  rec.List A (fun _ => Nat)
    zero
    (fun x xs ih => succ ih)
    xs

-- Fuel-based quicksort：结构递归在 fuel 上，可归纳证明
def quicksort_fuel (A : Type) (le : A -> A -> Bool) (fuel : Nat) (xs : List A) : List A :=
  rec.Nat (fun _ => List A -> List A)
    (fun xs => nil A)
    (fun fuel' ih => fun xs =>
      rec.List A (fun _ => List A)
        (nil A)
        (fun head tail _ =>
          list_append A (ih (list_filter A (fun x => not (le head x)) tail))
            (cons A head (ih (list_filter A (fun x => le head x) tail))))
        xs)
    fuel
    xs

-- 包装：用列表长度作为 fuel（足够保证正确计算）
def quicksort (A : Type) (le : A -> A -> Bool) (xs : List A) : List A :=
  quicksort_fuel A le (list_length A xs) xs

-- Nat 上的 <=
def nat_le (m n : Nat) : Bool := not (nat_gt m n)


def dec_le (a b : Decimal) : Bool := not (dec_lt b a)

def e0  : Decimal := nat_to_dec 3
def e1  : Decimal := nat_to_dec 1
def e2  : Decimal := nat_to_dec 4
def e3  : Decimal := nat_to_dec 1
def e4  : Decimal := nat_to_dec 5
def e5  : Decimal := nat_to_dec 9
def e6  : Decimal := nat_to_dec 2
def e7  : Decimal := nat_to_dec 6
def e8  : Decimal := nat_to_dec 5
def e9  : Decimal := nat_to_dec 3
def e10 : Decimal := nat_to_dec 5
def e11 : Decimal := nat_to_dec 8
def e12 : Decimal := nat_to_dec 9
def e13 : Decimal := nat_to_dec 7
def e14 : Decimal := nat_to_dec 9
def e15 : Decimal := nat_to_dec 3
def e16 : Decimal := nat_to_dec 2
def e17 : Decimal := nat_to_dec 3
def e18 : Decimal := nat_to_dec 8
def e19 : Decimal := nat_to_dec 4
def e20 : Decimal := nat_to_dec 6
def e21 : Decimal := nat_to_dec 2
def e22 : Decimal := nat_to_dec 6
def e23 : Decimal := nat_to_dec 4
def e24 : Decimal := nat_to_dec 3
def e25 : Decimal := nat_to_dec 3
def e26 : Decimal := nat_to_dec 8
def e27 : Decimal := nat_to_dec 3
def e28 : Decimal := nat_to_dec 2
def e29 : Decimal := nat_to_dec 7

def input_list : List Decimal :=
  cons Decimal e0 (
  cons Decimal e1 (
  cons Decimal e2 (
  cons Decimal e3 (
  cons Decimal e4 (
  cons Decimal e5 (
  cons Decimal e6 (
  cons Decimal e7 (
  cons Decimal e8 (
  cons Decimal e9 (
  cons Decimal e10 (
  cons Decimal e11 (
  cons Decimal e12 (
  cons Decimal e13 (
  cons Decimal e14 (
  cons Decimal e15 (
  cons Decimal e16 (
  cons Decimal e17 (
  cons Decimal e18 (
  cons Decimal e19 (
  cons Decimal e20 (
  cons Decimal e21 (
  cons Decimal e22 (
  cons Decimal e23 (
  cons Decimal e24 (
  cons Decimal e25 (
  cons Decimal e26 (
  cons Decimal e27 (
  cons Decimal e28 (
  cons Decimal e29 (nil Decimal))))))))))))))))))))))))))))))
