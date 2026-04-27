-- Multi-step solving example: using solve for equation derivation
-- Each step introduces constraints, ultimately determining the unknown value

import Nat
import Eq

-- Step 1: Declare an unknown natural number ?x
solve step1 : Nat := ?x

-- Step 2: Establish constraint ?x = zero
-- Through refl type unification, ?x is assigned the value zero
solve step2 : Eq Nat ?x zero := refl Nat zero

-- Step 3: Construct a new expression using the determined ?x
-- let a := ?x in succ a, the result should be succ zero
solve step3 : Nat := let a : Nat := ?x in succ a

-- Step 4: Prove that step3's result equals succ zero
solve step4 : Eq Nat (let a : Nat := ?x in succ a) (succ zero) := refl Nat (succ zero)
