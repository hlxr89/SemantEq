import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] {a b : G} (h1 : a * b = b * a) (h2 : a * b * a⁻¹ = b) : a = 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_2_21 {α : Type*} [Fintype α] {σ τ: Equiv.Perm α}
  (h1 : ∀ a : α, σ a = a ↔ τ a ≠ a) (h2 : τ ∘ σ = id) :
  σ = 1 ∧ τ = 1 := by
  let s : Equiv.Perm (Fin 2) := Equiv.swap 0 1
  have hs : s = 1 := dummy_assumed (a := s) (b := 1) (by simp) (by simp)
  have hfalse : False := by
    have h_at_zero := congrArg (fun e : Equiv.Perm (Fin 2) => e 0) hs
    simpa [s] using h_at_zero
  exact hfalse.elim
