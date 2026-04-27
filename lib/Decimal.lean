import Nat
import Eq
import True

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

-- -----------------------------------------------------------------
-- 3. 相等类型 Eq（带参数版本，支持 refl）
-- -----------------------------------------------------------------

def not (b : Bool) : Bool :=
  if b : Bool then false else true

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
    (if carry : Nat then succ zero else zero))

def digit_add_carry (d1 d2 : Digit) (carry : Bool) : Bool :=
  nat_gt (nat_add (nat_add (digit_to_nat d1) (digit_to_nat d2))
    (if carry : Nat then succ zero else zero))
    (succ (succ (succ (succ (succ (succ (succ (succ (succ zero)))))))))

def digit_eq (d1 d2 : Digit) : Bool :=
  nat_eq (digit_to_nat d1) (digit_to_nat d2)

def le_add (a b : List Digit) : List Digit :=
  rec.List Digit (fun _ => List Digit -> Bool -> List Digit)
    (fun b carry =>
      rec.List Digit (fun _ => Bool -> List Digit)
        (fun carry => if carry : List Digit then cons Digit d1 (nil Digit) else nil Digit)
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
        (fun db b' ih2 => if digit_eq da db : Bool then ih b' else false) b)
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

def nat_div_fuel (fuel : Nat) (m n : Nat) : Nat :=
  rec.Nat (fun _ => Nat -> Nat -> Nat)
    (fun m n => zero)
    (fun fuel' ih => fun m n =>
      if nat_gt n zero : Nat then
        if nat_gt m n : Nat then
          succ (ih (nat_sub m n) n)
        else
          if nat_eq m n : Nat then succ zero else zero
      else
        zero)
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
| make : Sign -> Decimal -> SignedDecimal

def sd_neg (sd : SignedDecimal) : SignedDecimal :=
  match sd : SignedDecimal with
  | make pos d => make neg d
  | make neg d => make pos d

def sd_abs (sd : SignedDecimal) : Decimal :=
  match sd : Decimal with | make _ d => d

def add_pos_neg (da db : Decimal) : SignedDecimal :=
  if dec_lt da db : SignedDecimal then make neg (dec_sub db da) else make pos (dec_sub da db)

def signed_dec_add (a b : SignedDecimal) : SignedDecimal :=
  match a : SignedDecimal with | make sa da =>
    match b : SignedDecimal with | make sb db =>
      rec.Sign (fun _ => SignedDecimal)
        (rec.Sign (fun _ => SignedDecimal)
          (make pos (dec_add da db))
          (add_pos_neg da db)
          sb)
        (rec.Sign (fun _ => SignedDecimal)
          (add_pos_neg db da)
          (make neg (dec_add da db))
          sb)
        sa

def signed_dec_sub (a b : SignedDecimal) : SignedDecimal :=
  signed_dec_add a (sd_neg b)

def signed_dec_mul (a b : SignedDecimal) : SignedDecimal :=
  match a : SignedDecimal with | make sa da =>
    match b : SignedDecimal with | make sb db =>
      rec.Sign (fun _ => SignedDecimal)
        (rec.Sign (fun _ => SignedDecimal)
          (make pos (dec_mul da db))
          (make neg (dec_mul da db))
          sb)
        (rec.Sign (fun _ => SignedDecimal)
          (make neg (dec_mul da db))
          (make pos (dec_mul da db))
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
      if dec_lt pa pb : FloatDecimal then
        pair Decimal Decimal (dec_add (float_pad da (dec_sub pb pa)) db) pb
      else
        pair Decimal Decimal (dec_add da (float_pad db (dec_sub pa pb))) pa

def float_sub (a b : FloatDecimal) : FloatDecimal :=
  match a : FloatDecimal with | pair Decimal Decimal da pa =>
    match b : FloatDecimal with | pair Decimal Decimal db pb =>
      if dec_lt pa pb : FloatDecimal then
        pair Decimal Decimal (dec_sub (float_pad da (dec_sub pb pa)) db) pb
      else
        pair Decimal Decimal (dec_sub da (float_pad db (dec_sub pa pb))) pa

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
    match exp_sd : FloatDecimal with | make sign exp_dec =>
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
    (fun x xs ih => if p x : List A then cons A x ih else ih)
    xs

-- 列表最大值（空列表返回默认值）
def list_max (A : Type) (le : A -> A -> Bool) (default : A) (xs : List A) : A :=
  rec.List A (fun _ => A)
    default
    (fun x xs ih => if le x ih : A then ih else x)
    xs

-- 列表最小值（空列表返回默认值）
def list_min (A : Type) (le : A -> A -> Bool) (default : A) (xs : List A) : A :=
  rec.List A (fun _ => A)
    default
    (fun x xs ih => if le x ih : A then x else ih)
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

-- -----------------------------------------------------------------
-- 20. 证明基础设施
-- -----------------------------------------------------------------

-- 逻辑合取
inductive And (P : Prop) (Q : Prop) : Prop where
| conj : P -> Q -> And P Q

-- Nat 列表有序谓词（递归定义，避免 indexed inductive 的 cases 限制）
def SortedNat (xs : List Nat) : Prop :=
  rec.List Nat (fun _ => Prop) True
    (fun x xs ih => rec.List Nat (fun _ => Prop) True
      (fun y ys ih2 => And (Eq Bool (nat_le x y) true) ih)
      xs)
    xs

-- Nat 列表最大值/最小值（空列表返回 zero）
def nat_list_max (xs : List Nat) : Nat := list_max Nat nat_le zero xs
def nat_list_min (xs : List Nat) : Nat := list_min Nat nat_le zero xs

-- 上界：列表中所有元素 <= pivot（即 max(xs) <= pivot）
def list_upper_bound (pivot : Nat) (xs : List Nat) : Prop :=
  Eq Bool (nat_le (nat_list_max xs) pivot) true

-- 下界：列表中所有元素 >= pivot（即 min(xs) >= pivot）
def list_lower_bound (pivot : Nat) (xs : List Nat) : Prop :=
  Eq Bool (nat_le pivot (nat_list_min xs)) true

-- 成员关系
def list_mem (x : Nat) (xs : List Nat) : Bool :=
  rec.List Nat (fun _ => Bool)
    false
    (fun y ys ih => if nat_eq x y : Bool then true else ih)
    xs

-- 基础引理：空列表有序
theorem sorted_nil : SortedNat (nil Nat) := by
  exact trivial

-- 基础引理：单元素列表有序
theorem sorted_single : forall (x : Nat), SortedNat (cons Nat x (nil Nat)) := by
  intro x
  exact trivial

-- nat_le 反射性（关键引理）
theorem nat_le_refl : forall (x : Nat), Eq Bool (nat_le x x) true :=
  rec.Nat (fun x : Nat => Eq Bool (nat_le x x) true)
    (refl Bool true)
    (fun x' : Nat => fun ih : Eq Bool (nat_le x' x') true => ih)

-- nat_le zero 最小元
theorem nat_le_zero_min : forall (n : Nat), Eq Bool (nat_le zero n) true :=
  rec.Nat (fun n : Nat => Eq Bool (nat_le zero n) true)
    (refl Bool true)
    (fun n' : Nat => fun ih : Eq Bool (nat_le zero n') true => refl Bool true)

-- 空列表的上界是任意 pivot
theorem upper_bound_nil : forall (pivot : Nat), list_upper_bound pivot (nil Nat) := by
  intro pivot
  exact refl Bool true

-- 两个元素有序
theorem sorted_two : forall (x y : Nat),
  Eq Bool (nat_le x y) true -> SortedNat (cons Nat x (cons Nat y (nil Nat))) := by
  intro x
  intro y
  intro h
  exact conj (Eq Bool (nat_le x y) true) True h trivial

-- 空列表的下界是 zero
theorem lower_bound_nil_zero : list_lower_bound zero (nil Nat) := by
  exact refl Bool true

-- Bool 双重否定
theorem bool_double_neg : forall (b : Bool), Eq Bool (not (not b)) b :=
  rec.Bool (fun b : Bool => Eq Bool (not (not b)) b)
    (refl Bool false)
    (refl Bool true)

-- -----------------------------------------------------------------
-- 21. 列表有序性判定（计算函数）
-- -----------------------------------------------------------------

-- 列表是否整体有序（非递减）
def is_sorted (xs : List Nat) : Bool :=
  rec.List Nat (fun _ => Bool) true
    (fun x xs ih => rec.List Nat (fun _ => Bool) true
      (fun y ys _ => rec.Bool (fun _ => Bool) false ih (nat_le x y))
      xs)
    xs


-- And 投影
def and_fst (P Q : Prop) (h : And P Q) : P :=
  rec.And P Q (fun _ => P) (fun p q => p) h

def and_snd (P Q : Prop) (h : And P Q) : Q :=
  rec.And P Q (fun _ => Q) (fun p q => q) h

-- 所有元素 <= pivot
def AllLeNat (pivot : Nat) (xs : List Nat) : Prop :=
  rec.List Nat (fun _ => Prop) True
    (fun x xs ih => And (Eq Bool (nat_le x pivot) true) ih)
    xs

-- 所有元素 >= pivot
def AllGeNat (pivot : Nat) (xs : List Nat) : Prop :=
  rec.List Nat (fun _ => Prop) True
    (fun x xs ih => And (Eq Bool (nat_le pivot x) true) ih)
    xs


-- all_le_append：append 保持 AllLeNat
def all_le_append (pivot : Nat) (xs ys : List Nat)
  (h1 : AllLeNat pivot xs) (h2 : AllLeNat pivot ys) : AllLeNat pivot (list_append Nat xs ys) :=
  rec.List Nat (fun zs : List Nat => AllLeNat pivot zs -> AllLeNat pivot (list_append Nat zs ys))
    (fun h1 : AllLeNat pivot (nil Nat) => h2)
    (fun x : Nat => fun xs' : List Nat => fun ih : AllLeNat pivot xs' -> AllLeNat pivot (list_append Nat xs' ys) => fun h_xs' : AllLeNat pivot (cons Nat x xs') =>
      conj (Eq Bool (nat_le x pivot) true) (AllLeNat pivot (list_append Nat xs' ys))
        (and_fst (Eq Bool (nat_le x pivot) true) (AllLeNat pivot xs') h_xs')
        (ih (and_snd (Eq Bool (nat_le x pivot) true) (AllLeNat pivot xs') h_xs')))
    xs
    h1

-- all_ge_append：append 保持 AllGeNat
def all_ge_append (pivot : Nat) (xs ys : List Nat)
  (h1 : AllGeNat pivot xs) (h2 : AllGeNat pivot ys) : AllGeNat pivot (list_append Nat xs ys) :=
  rec.List Nat (fun zs : List Nat => AllGeNat pivot zs -> AllGeNat pivot (list_append Nat zs ys))
    (fun h1 : AllGeNat pivot (nil Nat) => h2)
    (fun x : Nat => fun xs' : List Nat => fun ih : AllGeNat pivot xs' -> AllGeNat pivot (list_append Nat xs' ys) => fun h_xs' : AllGeNat pivot (cons Nat x xs') =>
      conj (Eq Bool (nat_le pivot x) true) (AllGeNat pivot (list_append Nat xs' ys))
        (and_fst (Eq Bool (nat_le pivot x) true) (AllGeNat pivot xs') h_xs')
        (ih (and_snd (Eq Bool (nat_le pivot x) true) (AllGeNat pivot xs') h_xs')))
    xs
    h1

-- filter_preserves_all_le：filter 保持 AllLeNat
def filter_preserves_all_le (pivot : Nat) (p : Nat -> Bool) (xs : List Nat)
  (h : AllLeNat pivot xs) : AllLeNat pivot (list_filter Nat p xs) :=
  rec.List Nat (fun ys : List Nat => AllLeNat pivot ys -> AllLeNat pivot (list_filter Nat p ys))
    (fun _ : AllLeNat pivot (nil Nat) => trivial)
    (fun x : Nat => fun xs' : List Nat => fun ih : AllLeNat pivot xs' -> AllLeNat pivot (list_filter Nat p xs') => fun h_xs : AllLeNat pivot (cons Nat x xs') =>
      rec.Bool (fun b : Bool => AllLeNat pivot (
        rec.Bool (fun _ : Bool => List Nat) (list_filter Nat p xs') (cons Nat x (list_filter Nat p xs')) b
      ))
        (ih (and_snd (Eq Bool (nat_le x pivot) true) (AllLeNat pivot xs') h_xs))
        (conj (Eq Bool (nat_le x pivot) true) (AllLeNat pivot (list_filter Nat p xs'))
          (and_fst (Eq Bool (nat_le x pivot) true) (AllLeNat pivot xs') h_xs)
          (ih (and_snd (Eq Bool (nat_le x pivot) true) (AllLeNat pivot xs') h_xs)))
        (p x))
    xs
    h

-- filter_preserves_all_ge：filter 保持 AllGeNat
def filter_preserves_all_ge (pivot : Nat) (p : Nat -> Bool) (xs : List Nat)
  (h : AllGeNat pivot xs) : AllGeNat pivot (list_filter Nat p xs) :=
  rec.List Nat (fun ys : List Nat => AllGeNat pivot ys -> AllGeNat pivot (list_filter Nat p ys))
    (fun _ : AllGeNat pivot (nil Nat) => trivial)
    (fun x : Nat => fun xs' : List Nat => fun ih : AllGeNat pivot xs' -> AllGeNat pivot (list_filter Nat p xs') => fun h_xs : AllGeNat pivot (cons Nat x xs') =>
      rec.Bool (fun b : Bool => AllGeNat pivot (
        rec.Bool (fun _ : Bool => List Nat) (list_filter Nat p xs') (cons Nat x (list_filter Nat p xs')) b
      ))
        (ih (and_snd (Eq Bool (nat_le pivot x) true) (AllGeNat pivot xs') h_xs))
        (conj (Eq Bool (nat_le pivot x) true) (AllGeNat pivot (list_filter Nat p xs'))
          (and_fst (Eq Bool (nat_le pivot x) true) (AllGeNat pivot xs') h_xs)
          (ih (and_snd (Eq Bool (nat_le pivot x) true) (AllGeNat pivot xs') h_xs)))
        (p x))
    xs
    h

-- filter_all_le：filter (fun x => x <= head) 的结果所有元素都 <= head
def filter_all_le (head : Nat) (xs : List Nat) : AllLeNat head (list_filter Nat (fun x => nat_le x head) xs) :=
  rec.List Nat (fun ys : List Nat => AllLeNat head (list_filter Nat (fun x => nat_le x head) ys))
    trivial
    (fun x : Nat => fun xs' : List Nat => fun ih : AllLeNat head (list_filter Nat (fun x => nat_le x head) xs') =>
      rec.Bool (fun b : Bool => forall (h : Eq Bool (nat_le x head) b), AllLeNat head (
        rec.Bool (fun _ : Bool => List Nat) (list_filter Nat (fun x => nat_le x head) xs') (cons Nat x (list_filter Nat (fun x => nat_le x head) xs')) b
      ))
        (fun _h : Eq Bool (nat_le x head) false => ih)
        (fun h : Eq Bool (nat_le x head) true =>
          conj (Eq Bool (nat_le x head) true) (AllLeNat head (list_filter Nat (fun x => nat_le x head) xs'))
            h
            ih)
        (nat_le x head)
        (refl Bool (nat_le x head)))
    xs

-- filter_all_ge：filter (fun x => head <= x) 的结果所有元素都 >= head
def filter_all_ge (head : Nat) (xs : List Nat) : AllGeNat head (list_filter Nat (fun x => nat_le head x) xs) :=
  rec.List Nat (fun ys : List Nat => AllGeNat head (list_filter Nat (fun x => nat_le head x) ys))
    trivial
    (fun x : Nat => fun xs' : List Nat => fun ih : AllGeNat head (list_filter Nat (fun x => nat_le head x) xs') =>
      rec.Bool (fun b : Bool => forall (h : Eq Bool (nat_le head x) b), AllGeNat head (
        rec.Bool (fun _ : Bool => List Nat) (list_filter Nat (fun x => nat_le head x) xs') (cons Nat x (list_filter Nat (fun x => nat_le head x) xs')) b
      ))
        (fun _h : Eq Bool (nat_le head x) false => ih)
        (fun h : Eq Bool (nat_le head x) true =>
          conj (Eq Bool (nat_le head x) true) (AllGeNat head (list_filter Nat (fun x => nat_le head x) xs'))
            h
            ih)
        (nat_le head x)
        (refl Bool (nat_le head x)))
    xs

-- sorted_cons_ge：cons pivot ys 有序，当 ys 有序且 pivot <= ys 的每个元素
def sorted_cons_ge (pivot : Nat) (ys : List Nat)
  (sorted_y : SortedNat ys) (ge_y : AllGeNat pivot ys) : SortedNat (cons Nat pivot ys) :=
  rec.List Nat (fun zs : List Nat => SortedNat zs -> AllGeNat pivot zs -> SortedNat (cons Nat pivot zs))
    (fun _ : SortedNat (nil Nat) => fun _ : AllGeNat pivot (nil Nat) => trivial)
    (fun y : Nat => fun ys' : List Nat => fun ih : SortedNat ys' -> AllGeNat pivot ys' -> SortedNat (cons Nat pivot ys') => fun sorted_y_ys' : SortedNat (cons Nat y ys') => fun ge_y_ys' : AllGeNat pivot (cons Nat y ys') =>
      conj (Eq Bool (nat_le pivot y) true) (SortedNat (cons Nat y ys'))
        (and_fst (Eq Bool (nat_le pivot y) true) (AllGeNat pivot ys') ge_y_ys')
        sorted_y_ys')
    ys
    sorted_y
    ge_y

-- sorted_tail：从 SortedNat (cons x xs') 提取 SortedNat xs'
def sorted_tail (x : Nat) (xs' : List Nat) (h : SortedNat (cons Nat x xs')) : SortedNat xs' :=
  rec.List Nat (fun zs : List Nat => SortedNat (cons Nat x zs) -> SortedNat zs)
    (fun _ : SortedNat (cons Nat x (nil Nat)) => trivial)
    (fun y : Nat => fun ys : List Nat => fun ih : SortedNat (cons Nat x ys) -> SortedNat ys => fun h : SortedNat (cons Nat x (cons Nat y ys)) =>
      and_snd (Eq Bool (nat_le x y) true) (SortedNat (cons Nat y ys)) h)
    xs'
    h

-- append_sorted_cons：append xs (cons pivot ys) 有序
def append_sorted_cons (xs : List Nat) (pivot : Nat) (ys : List Nat)
  (sorted_xs : SortedNat xs) (sorted_ys : SortedNat ys)
  (ge_ys : AllGeNat pivot ys) (le_xs : AllLeNat pivot xs) :
  SortedNat (list_append Nat xs (cons Nat pivot ys)) :=
  rec.List Nat (fun zs : List Nat => SortedNat zs -> AllLeNat pivot zs -> SortedNat (list_append Nat zs (cons Nat pivot ys)))
    (fun _ : SortedNat (nil Nat) => fun _ : AllLeNat pivot (nil Nat) => sorted_cons_ge pivot ys sorted_ys ge_ys)
    (fun x : Nat => fun xs' : List Nat => fun ih : SortedNat xs' -> AllLeNat pivot xs' -> SortedNat (list_append Nat xs' (cons Nat pivot ys)) => fun sorted_x_xs' : SortedNat (cons Nat x xs') => fun le_x_xs' : AllLeNat pivot (cons Nat x xs') =>
      let h_x_le_pivot : Eq Bool (nat_le x pivot) true := and_fst (Eq Bool (nat_le x pivot) true) (AllLeNat pivot xs') le_x_xs' in
      let h_xs'_le_pivot : AllLeNat pivot xs' := and_snd (Eq Bool (nat_le x pivot) true) (AllLeNat pivot xs') le_x_xs' in
      let h_sorted_xs' : SortedNat xs' := sorted_tail x xs' sorted_x_xs' in
      conj (Eq Bool (nat_le x pivot) true) (SortedNat (list_append Nat xs' (cons Nat pivot ys)))
        h_x_le_pivot
        (ih h_sorted_xs' h_xs'_le_pivot))
    xs
    sorted_xs
    le_xs

-- quicksort_preserves_all_le：quicksort 保持 AllLeNat
def quicksort_preserves_all_le (pivot : Nat) (fuel : Nat) (xs : List Nat)
  (h : AllLeNat pivot xs) : AllLeNat pivot (quicksort_fuel Nat nat_le fuel xs) :=
  rec.Nat (fun fuel' : Nat => forall (zs : List Nat), AllLeNat pivot zs -> AllLeNat pivot (quicksort_fuel Nat nat_le fuel' zs))
    (fun zs : List Nat => fun _ : AllLeNat pivot zs => trivial)
    (fun fuel' : Nat => fun ih : forall (zs : List Nat), AllLeNat pivot zs -> AllLeNat pivot (quicksort_fuel Nat nat_le fuel' zs) => fun zs : List Nat => fun h_zs : AllLeNat pivot zs =>
      rec.List Nat (fun ws : List Nat => AllLeNat pivot ws -> AllLeNat pivot (quicksort_fuel Nat nat_le (succ fuel') ws))
        (fun _ : AllLeNat pivot (nil Nat) => trivial)
        (fun head : Nat => fun tail : List Nat => fun _ : AllLeNat pivot tail -> AllLeNat pivot (quicksort_fuel Nat nat_le (succ fuel') tail) => fun h_tail : AllLeNat pivot (cons Nat head tail) =>
          let left := quicksort_fuel Nat nat_le fuel' (list_filter Nat (fun x => nat_le x head) tail) in
          let right := quicksort_fuel Nat nat_le fuel' (list_filter Nat (fun x => nat_le head x) tail) in
          let h_left := filter_all_le head tail in
          let h_right := filter_preserves_all_le pivot (fun x => nat_le head x) tail h_tail in
          let sorted_left := ih (list_filter Nat (fun x => nat_le x head) tail) (filter_preserves_all_le pivot (fun x => nat_le x head) tail h_tail) in
          let sorted_right := ih (list_filter Nat (fun x => nat_le head x) tail) h_right in
          let h_head_le := and_fst (Eq Bool (nat_le head pivot) true) (AllLeNat pivot tail) h_tail in
          all_le_append pivot left (cons Nat head right)
            sorted_left
            (conj (Eq Bool (nat_le head pivot) true) (AllLeNat pivot right)
              h_head_le
              sorted_right))
        zs
        h_zs)
    fuel
    xs
    h

-- quicksort_preserves_all_ge：quicksort 保持 AllGeNat
def quicksort_preserves_all_ge (pivot : Nat) (fuel : Nat) (xs : List Nat)
  (h : AllGeNat pivot xs) : AllGeNat pivot (quicksort_fuel Nat nat_le fuel xs) :=
  rec.Nat (fun fuel' : Nat => forall (zs : List Nat), AllGeNat pivot zs -> AllGeNat pivot (quicksort_fuel Nat nat_le fuel' zs))
    (fun zs : List Nat => fun _ : AllGeNat pivot zs => trivial)
    (fun fuel' : Nat => fun ih : forall (zs : List Nat), AllGeNat pivot zs -> AllGeNat pivot (quicksort_fuel Nat nat_le fuel' zs) => fun zs : List Nat => fun h_zs : AllGeNat pivot zs =>
      rec.List Nat (fun ws : List Nat => AllGeNat pivot ws -> AllGeNat pivot (quicksort_fuel Nat nat_le (succ fuel') ws))
        (fun _ : AllGeNat pivot (nil Nat) => trivial)
        (fun head : Nat => fun tail : List Nat => fun _ : AllGeNat pivot tail -> AllGeNat pivot (quicksort_fuel Nat nat_le (succ fuel') tail) => fun h_tail : AllGeNat pivot (cons Nat head tail) =>
          let left := quicksort_fuel Nat nat_le fuel' (list_filter Nat (fun x => nat_le x head) tail) in
          let right := quicksort_fuel Nat nat_le fuel' (list_filter Nat (fun x => nat_le head x) tail) in
          let h_left := filter_preserves_all_ge pivot (fun x => nat_le x head) tail h_tail in
          let h_right := filter_all_ge head tail in
          let sorted_left := ih (list_filter Nat (fun x => nat_le x head) tail) h_left in
          let sorted_right := ih (list_filter Nat (fun x => nat_le head x) tail) h_right in
          let h_head_ge := and_fst (Eq Bool (nat_le pivot head) true) (AllGeNat pivot tail) h_tail in
          all_ge_append pivot left (cons Nat head right)
            sorted_left
            (conj (Eq Bool (nat_le pivot head) true) (AllGeNat pivot right)
              h_head_ge
              sorted_right))
        zs
        h_zs)
    fuel
    xs
    h

-- 核心定理：quicksort_fuel 返回的列表总是有序的
def quicksort_fuel_sorted (fuel : Nat) (xs : List Nat) : SortedNat (quicksort_fuel Nat nat_le fuel xs) :=
  rec.Nat (fun fuel' : Nat => forall (zs : List Nat), SortedNat (quicksort_fuel Nat nat_le fuel' zs))
    (fun zs : List Nat => trivial)
    (fun fuel' : Nat => fun ih : forall (zs : List Nat), SortedNat (quicksort_fuel Nat nat_le fuel' zs) => fun zs : List Nat =>
      rec.List Nat (fun ws : List Nat => SortedNat (quicksort_fuel Nat nat_le (succ fuel') ws))
        (fun _ : SortedNat (quicksort_fuel Nat nat_le (succ fuel') (nil Nat)) => trivial)
        (fun head : Nat => fun tail : List Nat => fun _ : SortedNat (quicksort_fuel Nat nat_le (succ fuel') tail) => fun _ : SortedNat (quicksort_fuel Nat nat_le (succ fuel') (cons Nat head tail)) =>
          let left := quicksort_fuel Nat nat_le fuel' (list_filter Nat (fun x => nat_le x head) tail) in
          let right := quicksort_fuel Nat nat_le fuel' (list_filter Nat (fun x => nat_le head x) tail) in
          let sorted_left := ih (list_filter Nat (fun x => nat_le x head) tail) in
          let sorted_right := ih (list_filter Nat (fun x => nat_le head x) tail) in
          let le_left := quicksort_preserves_all_le head fuel' (list_filter Nat (fun x => nat_le x head) tail) (filter_all_le head tail) in
          let ge_right := quicksort_preserves_all_ge head fuel' (list_filter Nat (fun x => nat_le head x) tail) (filter_all_ge head tail) in
          append_sorted_cons left head right sorted_left (sorted_cons_ge head right sorted_right ge_right) ge_right le_left)
        zs)
    fuel
    xs

-- 顶层包装定理
theorem quicksort_sorted (xs : List Nat) : SortedNat (quicksort Nat nat_le xs) :=
  quicksort_fuel_sorted (list_length Nat xs) xs

