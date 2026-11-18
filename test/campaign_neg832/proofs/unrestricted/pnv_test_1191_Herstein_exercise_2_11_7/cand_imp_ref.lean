import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type u} [Group G] (P : Sylow p G) : Function.Injective (Subtype.val : P → G) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_11_7 {G : Type*} [Group G] {p : ℕ} (hp : Nat.Prime p)
  {P : Sylow p G} (hP : P.Normal) :
  Subgroup.Characteristic (P : Subgroup G) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : (P : Subgroup G).Normal := hP
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  have map_le (e : G ≃* G) : (P : Subgroup G).map e.toMonoidHom ≤ (P : Subgroup G) := by
    have hs : IsPGroup p ((P : Subgroup G).map e.toMonoidHom ⊔ (P : Subgroup G) : Subgroup G) :=
      (P.isPGroup'.map e.toMonoidHom).to_sup_of_normal_right P.isPGroup'
    have heq : (P : Subgroup G).map e.toMonoidHom ⊔ (P : Subgroup G) = (P : Subgroup G) :=
      P.is_maximal' hs le_sup_right
    exact le_sup_left.trans_eq heq
  apply le_antisymm (map_le φ)
  have h := Subgroup.map_mono (f := φ.toMonoidHom) (map_le φ.symm)
  simpa [Subgroup.map_map] using h
