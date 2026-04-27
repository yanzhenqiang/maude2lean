import Decimal

-- 3 elements
def t0 : Nat := 3
def t1 : Nat := 1
def t2 : Nat := 2

def tiny_input_list : List Nat :=
  cons Nat t0 (cons Nat t1 (cons Nat t2 (nil Nat)))
