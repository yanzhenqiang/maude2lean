-- 命题逻辑基础

inductive True : Prop where
| trivial : True

inductive False : Prop where

-- 否定
def Not (A : Prop) : Prop := A -> False
