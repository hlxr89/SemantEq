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
  letI : P.Normal := hP
  letI : Subsingleton (Sylow p G) :=
    ⟨fun Q R ↦ by
      have hPQ : IsPGroup p (P ⊔ Q : Subgroup G) :=
        P.isPGroup'.to_sup_of_normal_left Q.isPGroup'
      have hPR : IsPGroup p (P ⊔ R : Subgroup G) :=
        P.isPGroup'.to_sup_of_normal_left R.isPGroup'
      have hQ : (P : Subgroup G) = Q :=
        Q.is_maximal' P.isPGroup' (le_sup_right.trans_eq (P.is_maximal' hPQ le_sup_left))
      have hR : (P : Subgroup G) = R :=
        R.is_maximal' P.isPGroup' (le_sup_right.trans_eq (P.is_maximal' hPR le_sup_left))
      exact Sylow.ext (hQ.symm.trans hR)⟩
  exact Sylow.characteristic_of_subsingleton P
