/-
This part is mostly inspired by the `Natural Number Game`:
https://adam.math.hhu.de/#/g/leanprover-community/nng4
-/

import Mathlib.Tactic.Use
import Mathlib.Tactic.ByContra
import LeanBlockCourse26.P05_NaturalNumbers.S05_AdvancedAddition

/-
# Inequalities
=====================
-/

namespace MyNat

/-
## Inequality

We define `n ≤ m` as `∃ k, m = n + k`.
-/

def le (n m : MyNat) := ∃ k, m = n + k

/-
Note that lean defines `Nat.le` inductively ...

```
protected inductive Nat.le (n : Nat) : Nat → Prop
  | refl     : Nat.le n n
  | step {m} : Nat.le n m → Nat.le n (succ m)
```

... and then derives our notion as a theorem

```
protected theorem exists_eq_add_of_le (h : m ≤ n) : ∃ k : Nat, n = m + k :=
  ⟨n - m, (add_sub_of_le h).symm⟩
```
-/

-- The notation `≤` is unlocked through the `LE` type class 
instance : LE MyNat := ⟨MyNat.le⟩

theorem le_iff (m n : MyNat) : n ≤ m ↔ ∃ k, m = n + k :=
  by rfl

theorem le_refl (n : MyNat) : n ≤ n := by
  use 0
  rfl

theorem zero_le (n : MyNat) : 0 ≤ n := by
  use n
  rw [zero_add]

example (n : MyNat) : 0 ≤ n := by
  induction n with
  | zero => exact le_refl 0
  | succ i ih =>
    -- rw [le_iff] at *
    obtain ⟨k, ih⟩ := ih
    use k + 1
    simp [ih, succ_eq_add_one]

/-
We define `m < n` as `m + 1 ≤ n`. We will later show this is equivalent to `m ≤ n ∧ m ≠ n`.
-/

def lt (n m : MyNat) := (succ n) ≤ m

instance : LT MyNat := ⟨MyNat.lt⟩

theorem lt_iff (n m : MyNat) : n < m ↔ (succ n) ≤ m := by rfl

/-
## Exercise Block B01
-/

-- Exercise 1.1
theorem zero_lt (n : MyNat) (h : n ≠ 0) : 0 < n := by
  rw [lt_iff] -- optional
  cases n with
  | zero => contradiction
  | succ n => use n; rw [add_comm]; rfl

-- A slightly nicer proof first establishes this auxiliary lemma ...
theorem le_succ (m n : MyNat) : (m ≤ n) ↔ (m.succ ≤ n.succ) := by
  constructor <;> intro ⟨k, hk⟩ <;> use k
  · rw [succ_add, hk]
  · rw [succ_add, succ_inj] at hk; assumption

-- ...and use this
example (n : MyNat) (h : n ≠ 0) : 0 < n := by
  obtain ⟨k, hk⟩ := eq_succ_of_ne_zero h
  rw [hk, lt_iff, ← le_succ]
  exact zero_le k
  
example (n : MyNat) (h : n ≠ 0) : 0 < n := by
  obtain ⟨k, hk⟩ := eq_succ_of_ne_zero h
  simp [hk, lt_iff, ← le_succ, ]
  rw [zero_zero.symm] 
  exact zero_le k

-- Exercise 1.2 (Master)
theorem lt_iff_le_ne' (m n : MyNat) : m < n ↔ ∃k, k ≠ 0 ∧ m + k = n := by
  repeat rw [lt_iff, le_iff] -- optional
  constructor
  · intro h
    obtain ⟨k, h⟩ := h
    rw [succ_add, ← add_succ] at h
    use k.succ
    constructor
    · exact (zero_ne_succ k).symm 
    · exact h.symm
  · intro h
    obtain ⟨k, ⟨kn_zero, h⟩⟩ := h
    obtain ⟨k', hk'⟩ := eq_succ_of_ne_zero kn_zero
    use k'
    rw [succ_add, ← add_succ, ← hk']
    exact h.symm
    
example (m n : MyNat) : m < n ↔ ∃k, k ≠ 0 ∧ m + k = n := by
  simp [lt_iff, le_iff, add_succ]
  constructor
  · intro ⟨k, h⟩
    exact ⟨k.succ, (zero_ne_succ k).symm, h.symm⟩
  · intro ⟨k, ⟨kn_zero, h⟩⟩
    obtain ⟨k', hk'⟩ := eq_succ_of_ne_zero kn_zero
    exact ⟨k', add_succ m k' ▸ hk' ▸ h.symm⟩ 
    
-- example (m n : MyNat) : m < n ↔ ∃k, k ≠ 0 ∧ m + k = n := by
--   calc m < n
--       ↔ m.succ ≤ n            := lt_iff m n
--     _ ↔ ∃k, (n = m.succ + k)  := le_iff n m.succ
--     -- _ ↔ ∃k, (n = k + m.succ)  := by simp
--     -- _ ↔ ∃k, (n = succ (k + m)):= by simp
--     _ ↔ ∃k, n = m + (succ k)  := by simp
--     _ ↔ ∃k, k ≠ 0 ∧ m + k = n := by sorry

-- Exercise 1.3
theorem le_succ_self (n : MyNat) : n ≤ succ n := by
  sorry

-- Exercise 1.4
theorem le_trans {n m k : MyNat} (hnm : n ≤ m) (hmk : m ≤ k) : n ≤ k := by
  sorry

-- Exercise 1.5
theorem le_zero {n : MyNat} (hn : n ≤ 0) : n = 0 := by
  sorry

-- Exercise 1.6 (Master)
theorem le_antisymm (n m : MyNat) (hnm : n ≤ m) (hmn : m ≤ n) : n = m := by
  sorry

-- Exercise 1.7
theorem succ_le_succ {n m : MyNat} (hn : succ n ≤ succ m) : n ≤ m := by
  sorry

-- Exercise 1.8 (Master)
theorem le_one {n : MyNat} (hn : n ≤ 1) : n = 0 ∨ n = 1 := by
  sorry

-- Exercise 1.9 (Master)
theorem lt_iff_le_and_ne (m n : MyNat) : m < n ↔ m ≤ n ∧ m ≠ n := by
  sorry

-- Exercise 1.10 (Master)
theorem le_total (n m : MyNat) : n ≤ m ∨ m ≤ n := by
  sorry

end MyNat
