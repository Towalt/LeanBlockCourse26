/-
# S04: Verified Computation and Trust

The payoff: verified computation with Subtype, axiom tracing with
`#print axioms`, and the trust model.
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Prime.Basic




-- #check Inhabited

-- def get_default (α : Type*) [Inhabited α] : α := @Inhabited.default α _
 
-- instance : Inhabited Nat where 
-- | default => 0

-- #print get_default Nat


/-!
## Verified computation

The pattern:
1. Write an algorithm with a plain type signature.
2. Prove a property as a separate theorem.
3. Bundle into Subtype — the return type carries the guarantee.
-/

section VerifiedFilter

variable {α : Type}

-- Step 1: algorithm. `[DecidablePred p]` lets `if` branch on a Prop.

/-
`List` is defined inductively on lean with constructors for an empty
list (`nil`) and an dependent constructor `cons` that appends and element
`(head : α)` to a given existing list `(tail : List α)`.

inductive List (α : Type u) where
  | nil : List α 
  | cons (head : α) (tail : List α) : List α

We can use `[...]` notation with `[] = List.nil`
-/

def propFilter (p : α → Prop) [DecidablePred p] : List α → List α
  | [] => [] 
  | head :: tail =>
      let filtered_tail := propFilter p tail
      if (p head) then
        head :: filtered_tail
      else
        filtered_tail

-- We can actually evaluate this computationally ...
#eval propFilter (fun n : Nat => n  % 2 = 0)  [1, 2, 3, 4, 5, 6]


-- ... but only if we know `DecidablePred` holds and is computable
def p_nat_even := (fun n : Nat => n  % 2 = 0) 

noncomputable instance : DecidablePred p_nat_even := Classical.decPred p_nat_even

-- instance : DecidablePred p_nat_even := by
--   intro n
--   | isFalse => sorry
--   | isTrue => sorry

-- Complains about `Classical.choice` axiom being used
-- #eval propFilter p_nat_even [1, 2, 3, 4, 5, 6]

-- Exercise: prove that `propFilter` is sound
-- Step 2a: prove soundness — everything in the output satisfies p.
theorem propFilter_sound (p : α → Prop) [DecidablePred p] (xs : List α) :
    ∀ x ∈ propFilter p xs, p x := by
  sorry

-- Step 2b: prove completeness - everyhting not in the output does not satisfy p.
-- theorem propFilter_complete (p : α → Prop) [DecidablePred p] (xs : List α) :
--     ∀ x ∈ propFilter p xs, p x := by
--   sorry

-- Step 3: bundle algorithm + proof into Subtype.
def verifiedFilter (p : α → Prop) [DecidablePred p] (xs : List α) :
    { ys : List α // ∀ x ∈ ys, p x } :=
  ⟨propFilter p xs, propFilter_sound p xs⟩

-- #eval (verifiedFilter (fun n : Nat => n % 2 = 0) [1, 2, 3, 4, 5, 6]).val




end VerifiedFilter
