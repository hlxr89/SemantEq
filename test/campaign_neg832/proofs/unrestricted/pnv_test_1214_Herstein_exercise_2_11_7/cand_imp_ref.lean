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
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  apply SetLike.ext'
  simpa only [Subgroup.coe_map, MonoidHom.coe_coe, EquivLike.coe_coe]
    using dummy_assumed P.isPGroup' φ
