import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] [Fintype G] {p : ℕ} [hp : Fact p.Prime] {P : Sylow p G} (f : G ≃* G) : ↑f '' P = P := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_11_7 {G : Type*} [Group G] {p : ℕ} (hp : Nat.Prime p)
  {P : Sylow p G} (hP : P.Normal) :
  Subgroup.Characteristic (P : Subgroup G) := by
  letI : (P : Subgroup G).Normal := hP
  rw [Subgroup.characteristic_iff_map_le]
  intro f
  let Q : Subgroup G := (P : Subgroup G).map f.toMonoidHom
  have hQ : IsPGroup p Q := P.isPGroup'.map f.toMonoidHom
  have hsup : IsPGroup p (↑P ⊔ Q : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left P.isPGroup' hQ
  have heq : (↑P ⊔ Q : Subgroup G) = P := P.is_maximal' hsup le_sup_left
  change Q ≤ (P : Subgroup G)
  rw [← heq]
  exact le_sup_right
