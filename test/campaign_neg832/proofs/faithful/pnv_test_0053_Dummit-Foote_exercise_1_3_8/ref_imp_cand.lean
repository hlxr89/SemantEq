import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1_3_8_assumed : Infinite (Equiv.Perm ℕ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (Ω : Type*) [Infinite Ω] : Infinite (Equiv.Perm Ω) := by
  apply @Infinite.of_injective (Equiv.Perm Ω) (Equiv.Perm ℕ) exercise_1_3_8_assumed
    (Equiv.Perm.viaEmbeddingHom (Infinite.natEmbedding Ω))
  exact Equiv.Perm.viaEmbeddingHom_injective _
