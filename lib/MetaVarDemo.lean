-- 多步求解示例：利用 solve 进行方程推导
-- 每一步引入约束，最终确定未知量的值

import Nat
import Eq

-- 步骤1：声明一个未知自然数 ?x
solve step1 : Nat := ?x

-- 步骤2：建立约束 ?x = zero
-- 通过 refl 的类型统一，?x 被赋值为 zero
solve step2 : Eq Nat ?x zero := refl Nat zero

-- 步骤3：使用已确定的 ?x 构造新表达式
-- let a := ?x in succ a，结果应为 succ zero
solve step3 : Nat := let a : Nat := ?x in succ a

-- 步骤4：证明 step3 的结果等于 succ zero
solve step4 : Eq Nat (let a : Nat := ?x in succ a) (succ zero) := refl Nat (succ zero)
