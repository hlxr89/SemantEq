import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime] {P : Sylow p G} (hP : IsPGroup p P) (φ : G ≃* G) : φ.toEquiv '' P = P := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_11_7 {G : Type*} [Group G] {p : ℕ} (hp : Nat.Prime p)
  {P : Sylow p G} (hP : P.Normal) :
  Subgroup.Characteristic (P : Subgroup G) := by
  letI : Fact p.Prime := ⟨hp⟩
  constructor
  intro φ
  have himage := dummy_assumed P.isPGroup' φ
  ext x
  constructor
  · intro hx
    change φ x ∈ P at hx
    have hx' : φ x ∈ φ.toEquiv '' (P : Set G) := by
      rw [himage]
      exact hx
    obtain ⟨y, hy, hxy⟩ := hx'
    have hyx : y = x := φ.injective hxy
    simpa [hyx] using hy
  · intro hx
    change φ x ∈ P
    have hx' : φ x ∈ φ.toEquiv '' (P : Set G) := ⟨x, hx, rfl⟩
    rw [himage] at hx'
    exact hx'
