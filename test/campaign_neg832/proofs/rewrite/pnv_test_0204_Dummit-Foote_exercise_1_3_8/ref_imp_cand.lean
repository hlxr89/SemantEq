import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1_3_8_assumed : Infinite (Equiv.Perm ℕ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (Ω : Type*) (hΩ : Infinite Ω) : Infinite (Equiv.Perm Ω) := by
  letI : Infinite Ω := hΩ
  letI : Infinite (Equiv.Perm ℕ) := exercise_1_3_8_assumed
  exact Infinite.of_injective -- non-rewrite step
    (Equiv.Perm.viaEmbeddingHom (Infinite.natEmbedding Ω))
    (Equiv.Perm.viaEmbeddingHom_injective (Infinite.natEmbedding Ω))
