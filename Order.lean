-- Nat 上的序关系（归纳族）
-- le m n 表示 m <= n

inductive le : Nat -> Nat -> Prop where
| le_zero : forall (n : Nat), le zero n
| le_succ : forall (m : Nat), forall (n : Nat), le m n -> le (succ m) (succ n)

-- 基于 le 定义其他序关系
def lt (m : Nat) (n : Nat) : Prop := le (succ m) n
def ge (m : Nat) (n : Nat) : Prop := le n m
def gt (m : Nat) (n : Nat) : Prop := lt n m

-- Nat 上的绝对值（简单版本：由于 Nat 没有负数，abs 就是恒等）
def abs_nat (n : Nat) : Nat := n
