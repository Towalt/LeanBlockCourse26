/-
This part is mostly inspired by the `Natural Number Game`:
https://adam.math.hhu.de/#/g/leanprover-community/nng4
-/

import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Tauto
import LeanBlockCourse26.P05_NaturalNumbers.S06_Inequalities

/-
# Advanced Multiplication
=====================
-/

namespace MyNat

/-
## Exercise Block B01
-/

-- Exercise 1.1
theorem mul_le_mul_right {n m : MyNat} (k : MyNat) (h : n ≤ m) : n * k ≤ m * k := by
  sorry

-- Exercise 1.2
theorem one_le_of_ne_zero {n : MyNat} (hn : n ≠ 0) : 1 ≤ n := by
  sorry

-- Exercise 1.3
theorem mul_left_ne_zero {n m : MyNat} (h : n * m ≠ 0) : m ≠ 0 := by
  sorry

-- Exercise 1.4
theorem le_mul_right {n m : MyNat} (h : n * m ≠ 0) : n ≤ n * m := by
  sorry

-- Exercise 1.5 (Master)
theorem mul_right_eq_one {n m : MyNat} (h : n * m = 1) : n = 1 := by
  sorry

-- Exercise 1.6 (Master)
theorem mul_ne_zero {n m : MyNat} (hn : n ≠ 0) (hm : m ≠ 0) : n * m ≠ 0 := by
  sorry

-- Exercise 1.7 (Master)
theorem mul_eq_zero {n m : MyNat} (h : n * m = 0) : n = 0 ∨ m = 0 := by
  sorry

/-
## A challenging induction: `induction` while `generalizing`
-/

-- Try proving this with `induction m`
theorem mul_left_cancel {n m k : MyNat}
    (hn : n ≠ 0) (h : n * m = n * k) : m = k := by
  revert k -- `h` is automatically also reverted since it depends on `k`
  induction m with
  | zero =>
      intro k h
      rw [← zero_zero, mul_zero] at h
      obtain f₁ | f₂ :=  mul_eq_zero h.symm
      · contradiction
      · exact f₂.symm
  | succ m ih =>
    /-
    If we did not `revert k` before the induction, then we would have
    `ih : n * m = n * k → m = k` for the *specific*  `k` that we are 
    trying to show the inductive step for. However, since 
    `h : n * m.succ = n * k`, we know that `n * m ≠ n * k` and `ih`
    becomes useless...
    -/ 
    intro k h 
    cases k with
    | zero => 
        exfalso
        rw [← zero_zero, mul_zero] at h
        have h' := add_left_eq_zero h
        contradiction
    | succ => 
        rw [mul_succ, mul_succ] at h
         -- Here we finally use the inductive assumption!
        rw [ih (add_right_cancel h)]


-- In fact `induction ... generalizing ...` wraps the `revert` / `intro` dance for us
example {n m k : MyNat}
    (hn : n ≠ 0) (h : n * m = n * k) : m = k := by
  induction m generalizing k with
  | zero =>
      rw [← zero_zero, mul_zero] at h
      obtain f₁ | f₂ :=  mul_eq_zero h.symm
      · contradiction
      · exact f₂.symm
  | succ m ih =>
    cases k with
    | zero => 
        exfalso
        rw [← zero_zero, mul_zero] at h
        have h' := add_left_eq_zero h
        contradiction
    | succ => 
        rw [mul_succ, mul_succ] at h
         -- Here we finally use the inductive assumption!
        rw [ih (add_right_cancel h)]
    
end MyNat
