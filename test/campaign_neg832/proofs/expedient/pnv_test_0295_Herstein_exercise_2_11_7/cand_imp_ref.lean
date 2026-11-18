import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (G : Type*) [Group G] {P : Subgroup G} (hP : IsPGroup p P) (hPn : P.Normal) (hPs : IsPGroup p (G ⧸ P)) : ∀ (φ : G →* G), φ.range = P := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_11_7 {G : Type*} [Group G] {p : ℕ} (hp : Nat.Prime p)
  {P : Sylow p G} (hP : P.Normal) :
  Subgroup.Characteristic (P : Subgroup G) := by
  letI := hP
  refine Subgroup.characteristic_iff_map_le.mpr fun φ ↦ ?_
  have hs : IsPGroup p (((P : Subgroup G).map φ.toMonoidHom ⊔ (P : Subgroup G)) : Subgroup G) :=
    (P.isPGroup'.map φ.toMonoidHom).to_sup_of_normal_right P.isPGroup'
  have heq : (P : Subgroup G).map φ.toMonoidHom ⊔ P = P :=
    P.is_maximal' hs le_sup_right
  exact le_sup_left.trans_eq heq
