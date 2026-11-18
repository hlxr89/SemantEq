import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {α : Type*} [DecidableEq α] {σ τ : Equiv.Perm α} (h : ∀ x, σ x ≠ τ x) (h' : σ * τ = 1) : σ = 1 ∧ τ = 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_2_21 {α : Type*} [Fintype α] {σ τ: Equiv.Perm α}
  (h1 : ∀ a : α, σ a = a ↔ τ a ≠ a) (h2 : τ ∘ σ = id) :
  σ = 1 ∧ τ = 1 := by
  have hτσ (a : α) : τ (σ a) = a := by
    simpa using congrFun h2 a
  have noelem : ∀ a : α, False := by
    intro a
    have hfixed : σ a = a ↔ τ a = a := by
      constructor
      · intro hs
        calc
          τ a = τ (σ a) := congrArg τ hs.symm
          _ = a := hτσ a
      · intro ht
        apply τ.injective
        calc
          τ (σ a) = a := hτσ a
          _ = τ a := ht.symm
    by_cases hs : σ a = a
    · exact (h1 a).mp hs (hfixed.mp hs)
    · have ht : τ a ≠ a := fun hta => hs (hfixed.mpr hta)
      exact hs ((h1 a).mpr ht)
  constructor
  · ext a
    exact (noelem a).elim
  · ext a
    exact (noelem a).elim
