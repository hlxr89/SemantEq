import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_3_2_21_assumed {α : Type*} [Fintype α] {σ τ: Equiv.Perm α}
  (h1 : ∀ a : α, σ a = a ↔ τ a ≠ a) (h2 : τ ∘ σ = id) :
  σ = 1 ∧ τ = 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {α : Type*} [Fintype α] {σ τ : Equiv.Perm α} (h : ∀ x, σ x ≠ x → τ x = x) (hστ : σ * τ = 1) : σ = 1 ∧ τ = 1 := by
  have hc (x : α) : σ (τ x) = x := by
    have hx := DFunLike.congr_fun hστ x
    simpa using hx
  have hs (x : α) : σ x = x := by
    by_contra hx
    have ht := h x hx
    exact hx (by simpa [ht] using hc x)
  constructor <;> ext x
  · simpa using hs x
  · calc
      τ x = σ (τ x) := (hs (τ x)).symm
      _ = x := hc x
