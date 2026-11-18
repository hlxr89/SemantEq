import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {Ω : Type*} [Infinite Ω] : Infinite (Sym2 Ω) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_3_8 : Infinite (Equiv.Perm ℕ) := by
  letI : Infinite (Sym2 ℕ) := dummy_assumed (Ω := ℕ)
  refine Infinite.of_injective
    (fun x : Sym2 ℕ =>
      Equiv.swap 0 (Encodable.encode (Sym2.equivMultiset ℕ x) + 1)) ?_
  exact (Equiv.swap_injective_of_left 0).comp
    (Nat.succ_injective.comp
      (Encodable.encode_injective.comp (Sym2.equivMultiset ℕ).injective))
