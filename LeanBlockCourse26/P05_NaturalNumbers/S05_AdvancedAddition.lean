/-
This part is mostly inspired by the `Natural Number Game`:
https://adam.math.hhu.de/#/g/leanprover-community/nng4
-/

import LeanBlockCourse26.P05_NaturalNumbers.S04_Power

/-
# Advanced Addition
=====================
-/

namespace MyNat

/-
## Exercise Block B01
-/

-- Exercise 1.1 
theorem add_right_cancel {n m k : MyNat} (h : n + k = m + k) : n = m := by
  induction k with
  | zero => assumption -- just does `exact h`
  | succ i ih => exact ih (succ_inj.mp h) 

-- Exercise 1.2
theorem add_left_cancel {n m k : MyNat} (h : k + n = k + m) : n = m := by
  repeat rw [add_comm k] at h
  exact add_right_cancel h

example {n m k : MyNat} (h : k + n = k + m) : n = m := by
  simp only [add_comm] at h
  exact add_right_cancel h

-- Exercise 1.3
theorem add_left_eq_self {n m : MyNat} (h : n + m = m) : n = 0 := by
  nth_rw 2 [← zero_add m] at h
  exact add_right_cancel h

example {n m : MyNat} (h : n + m = n) : m = 0 := by
  induction n <;> simp only [add_comm] at h
  · assumption
  · exact add_left_eq_self h

-- Exercise 1.4 (Master)
theorem add_right_eq_zero {n m : MyNat} (h : n + m = 0) : n = 0 := by
  cases m
  · assumption
  · contradiction

-- Exercise 1.5 (Master)
theorem add_left_eq_zero {n m : MyNat} (h : n + m = 0) : m = 0 := by
  rw [add_comm] at h
  exact add_right_eq_zero h

end MyNat
