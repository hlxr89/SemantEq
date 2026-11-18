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
  classical
  letI : Infinite (Equiv.Perm ℕ) := exercise_1_3_8_assumed
  letI := hΩ
  let e : ℕ ↪ Ω := Infinite.natEmbedding Ω
  let f : ℕ ≃ {x // x ∈ Set.range e} := Equiv.ofInjective e e.injective
  apply Infinite.of_injective (fun σ : Equiv.Perm ℕ => σ.extendDomain f)
  intro σ τ hστ
  apply Equiv.ext
  intro n
  apply e.injective
  calc
    e (σ n) = (σ.extendDomain f) (e n) := by
      rw [← show (f n : Ω) = e n from rfl]
      rw [Equiv.Perm.extendDomain_apply_image σ f n]
      rfl
    _ = (τ.extendDomain f) (e n) := DFunLike.congr_fun hστ (e n)
    _ = e (τ n) := by
      rw [← show (f n : Ω) = e n from rfl]
      rw [Equiv.Perm.extendDomain_apply_image τ f n]
      rfl
