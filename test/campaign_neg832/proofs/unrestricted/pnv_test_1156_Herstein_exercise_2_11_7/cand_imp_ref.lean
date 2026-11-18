import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- The unified context is empty.

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] {p : ℕ} {P : Subgroup G} [hp : Fact p.Prime] (hP : P.Normal) (hSylow : IsPGroup p P) (ϕ : G ≃* G) : ϕ.toMonoidHom '' P = P := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_11_7 {G : Type*} [Group G] {p : ℕ} (hp : Nat.Prime p)
  {P : Sylow p G} (hP : P.Normal) :
  Subgroup.Characteristic (P : Subgroup G) := by
  letI : Fact p.Prime := ⟨hp⟩
  constructor
  intro ϕ
  apply SetLike.ext
  intro x
  change ϕ x ∈ (P : Subgroup G) ↔ x ∈ (P : Subgroup G)
  have hfix : ϕ.toMonoidHom '' (P : Subgroup G) = (P : Subgroup G) :=
    dummy_assumed hP P.isPGroup' ϕ
  have hmem : ϕ x ∈ ϕ.toMonoidHom '' (P : Subgroup G) ↔ x ∈ (P : Subgroup G) := by
    simp
  rw [hfix] at hmem
  exact hmem
