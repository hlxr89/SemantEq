import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] [Fintype G] (h : Fintype.card G = 2^4 * 7) : ∃ H : Subgroup G, H ≠ ⊥ ∧ H ≠ ⊤ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_6_4_12 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 224) :
  IsSimpleGroup G → false := by
  intro hs
  letI : IsSimpleGroup G := hs
  let P : Sylow 2 G := Classical.choice inferInstance
  have hGnat : Nat.card G = 224 := by
    rw [Nat.card_eq_fintype_card]
    exact hG
  have hPcard : Nat.card (P : Subgroup G) = 32 := by
    rw [P.card_eq_multiplicity, hGnat]
    native_decide
  have hPne : (P : Subgroup G) ≠ ⊤ := by
    intro hPtop
    have := hPcard
    rw [hPtop, Subgroup.card_top, hGnat] at this
    norm_num at this
  have hcore : (P : Subgroup G).normalCore = ⊥ := by
    rcases (P : Subgroup G).normalCore_normal.eq_bot_or_eq_top with hbot | htop
    · exact hbot
    · exfalso
      apply hPne
      apply top_unique
      rw [← htop]
      exact (P : Subgroup G).normalCore_le
  let φ := MulAction.toPermHom G (G ⧸ (P : Subgroup G))
  have hker : φ.ker = ⊥ := by
    rw [← (P : Subgroup G).normalCore_eq_ker]
    exact hcore
  have hinj : Function.Injective φ := φ.ker_eq_bot_iff.mp hker
  have hdvd := card_dvd_of_injective φ hinj
  have hindex : (P : Subgroup G).index = 7 := by
    have hm := (P : Subgroup G).card_mul_index
    rw [hPcard, hGnat] at hm
    omega
  rw [Nat.card_perm, ← (P : Subgroup G).index_eq_card, hindex, hGnat] at hdvd
  norm_num at hdvd
