import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 351) : ∃ p : ℕ, ∃ P : Sylow p G, P.toSubgroup.Normal := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_5_15 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 351) :
  ∃ (p : ℕ) (P : Sylow p G), p.Prime ∧ (p ∣ card G) ∧  P.Normal := by
  let _ := dummy_assumed G hG
  have hp13 : Nat.Prime 13 := by norm_num
  letI : Fact (Nat.Prime 13) := ⟨hp13⟩
  let P : Sylow 13 G := default
  have hcardP : Nat.card P = 13 := by
    rw [P.card_eq_multiplicity, Nat.card_eq_fintype_card, hG]
    have hv : padicValNat 13 351 = 1 := by native_decide
    rw [show Nat.factorization 351 13 = padicValNat 13 351 by rfl, hv]
    norm_num
  have hindexP : P.index = 27 := by
    have := P.index_mul_card
    rw [hcardP, Nat.card_eq_fintype_card, hG] at this
    omega
  have hn_dvd : Nat.card (Sylow 13 G) ∣ 27 := by
    simpa [hindexP] using P.card_dvd_index
  have hn_mod : Nat.card (Sylow 13 G) ≡ 1 [MOD 13] := card_sylow_modEq_one 13 G
  have hn : Nat.card (Sylow 13 G) = 1 ∨ Nat.card (Sylow 13 G) = 27 := by
    have hn_le : Nat.card (Sylow 13 G) ≤ 27 :=
      Nat.le_of_dvd (by norm_num) hn_dvd
    interval_cases h : Nat.card (Sylow 13 G)
    all_goals first | exact Or.inl rfl | exact Or.inr rfl |
      (norm_num at hn_mod <;> norm_num at hn_dvd)
  rcases hn with hn | hn
  · haveI : Subsingleton (Sylow 13 G) :=
      (Nat.card_eq_one_iff_unique.mp hn).1
    exact ⟨13, P, hp13, by norm_num [hG], P.normal_of_subsingleton⟩
  · have hcardN : Nat.card P.normalizer = 13 := by
      have hi : P.normalizer.index = 27 := by
        rw [← P.card_eq_index_normalizer, hn]
      have hm := P.normalizer.index_mul_card
      rw [hi] at hm
      have hcG : Nat.card G = 351 := by simpa using hG
      rw [hcG] at hm
      omega
    have hNP : P.normalizer = (P : Subgroup G) := by
      apply SetLike.coe_injective
      symm
      exact Set.Finite.eq_of_subset_of_card_le (Set.toFinite _) P.le_normalizer
        (by simpa [hcardP] using hcardN.le)
    have hcent : (P : Subgroup G).normalizer ≤ Subgroup.centralizer (P : Set G) := by
      rw [hNP]
      letI : IsCyclic P := isCyclic_of_prime_card hcardP
      letI : CommGroup P := IsCyclic.commGroup
      intro x hx y hy
      exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : P) ⟨y, hy⟩).symm
    let K : Subgroup G := (MonoidHom.transferSylow P hcent).ker
    have hcomp : K.IsComplement' P := MonoidHom.ker_transferSylow_isComplement' P hcent
    have hcardK : Nat.card K = 27 := by
      have hm := hcomp.card_mul
      rw [hcardP] at hm
      have hcG : Nat.card G = 351 := by simpa using hG
      rw [hcG] at hm
      omega
    have hp3 : Nat.Prime 3 := by norm_num
    letI : Fact (Nat.Prime 3) := ⟨hp3⟩
    let Q : Sylow 3 G := Sylow.ofCard K (by
      rw [hcardK, Nat.card_eq_fintype_card, hG]
      have hv : padicValNat 3 351 = 3 := by native_decide
      rw [show Nat.factorization 351 3 = padicValNat 3 351 by rfl, hv]
      norm_num)
    have hnormalK : K.Normal := inferInstance
    exact ⟨3, Q, hp3, by norm_num [hG], hnormalK⟩
