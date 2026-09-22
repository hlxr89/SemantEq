import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed : ¬ Summable (fun n => if H : Squarefree n then 1 / n else 0) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_27a :
  ¬ Summable (λ i : {p : ℤ // Squarefree p} => (1 : ℚ) / i) := by
  exfalso
  apply dummy_assumed
  apply summable_of_finite_support
  refine (Set.finite_singleton 1).subset ?_
  intro n hn
  simp only [Function.mem_support, ne_eq, Set.mem_singleton_iff] at hn ⊢
  by_contra hne
  apply hn
  split
  · rename_i H
    have hn0 : n = 0 ∨ 1 < n := by omega
    rcases hn0 with rfl | hn2
    · simp
    · exact Nat.div_eq_of_lt hn2
  · rfl
