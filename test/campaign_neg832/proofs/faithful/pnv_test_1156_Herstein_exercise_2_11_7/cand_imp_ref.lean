import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] {p : ℕ} {P : Subgroup G} [hp : Fact p.Prime] (hP : P.Normal) (hSylow : IsPGroup p P) (ϕ : G ≃* G) : ϕ.toMonoidHom '' P = P := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_11_7 {G : Type*} [Group G] {p : ℕ} (hp : Nat.Prime p)
  {P : Sylow p G} (hP : P.Normal) :
  Subgroup.Characteristic (P : Subgroup G) := by
  letI : Fact p.Prime := ⟨hp⟩
  apply Subgroup.characteristic_iff_map_eq.mpr
  intro ϕ
  apply SetLike.ext'
  simpa using
    (dummy_assumed (G := G) (p := p) (P := (P : Subgroup G)) hP P.isPGroup' ϕ)
