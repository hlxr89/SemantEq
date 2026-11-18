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
  letI : (P : Subgroup G).Normal := hP
  have huniq : ∀ Q : Sylow p G, Q = P := by
    intro Q
    have hsup : IsPGroup p ((P : Subgroup G) ⊔ (Q : Subgroup G) : Subgroup G) :=
      P.isPGroup'.to_sup_of_normal_left Q.isPGroup'
    have hle : (Q : Subgroup G) ≤ (P : Subgroup G) := by
      rw [← P.is_maximal' hsup le_sup_left]
      exact le_sup_right
    exact Sylow.ext (Q.is_maximal' P.isPGroup' hle).symm
  letI : Subsingleton (Sylow p G) :=
    ⟨fun Q R ↦ (huniq Q).trans (huniq R).symm⟩
  exact Sylow.characteristic_of_subsingleton P
