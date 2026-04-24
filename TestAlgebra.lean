-- 测试代数运算

-- 测试 frac_neg: -(3) = -3
solve test_neg : Eq Frac (frac_neg (nat_to_frac 3)) (int_to_frac (negSucc 2)) := refl Frac (int_to_frac (negSucc 2))

-- 测试 square: 3² = 9
solve test_square : Eq Frac (square (nat_to_frac 3)) (nat_to_frac 9) := refl Frac (nat_to_frac 9)

-- 测试 frac_div: 6/2 = 3
solve test_div : Eq Frac (frac_div (nat_to_frac 6) (nat_to_frac 2)) (nat_to_frac 3) := refl Frac (nat_to_frac 3)

-- 测试复合运算: (-2)² = 4
solve test_neg_square : Eq Frac (square (frac_neg (nat_to_frac 2))) (nat_to_frac 4) := refl Frac (nat_to_frac 4)
