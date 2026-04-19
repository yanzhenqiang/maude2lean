-- 等式归纳族
-- Eq A a b 表示在类型 A 中 a = b

inductive Eq (A : Type) (a : A) : A -> Prop where
| refl : Eq A a a
