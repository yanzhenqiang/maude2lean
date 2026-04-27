-- Propositional logic basics

inductive True : Prop where
| trivial : True

inductive False : Prop where

inductive Or (A : Prop) (B : Prop) : Prop where
| inl : A -> Or A B
| inr : B -> Or A B

-- Negation
def Not (A : Prop) : Prop := A -> False
