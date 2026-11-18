import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] [Fintype G] : Fintype.card G = 56 → ∃ (p : ℕ)(H : Sylow p G), H.Normal := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_5_13 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 56) :
  ∃ (p : ℕ) (P : Sylow p G), p.Prime ∧ (p ∣ card G) ∧ P.Normal := by
  classical
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let P : Sylow 7 G := default
  have hcardG : Nat.card G = 56 := Nat.card_eq_fintype_card.trans hG
  have hcardP : Nat.card P = 7 := by
    rw [Sylow.card_eq_multiplicity, hcardG]
    native_decide
  have hindexP : (P : Subgroup G).index = 8 := by
    have h := Subgroup.card_mul_index (P : Subgroup G)
    rw [hcardP, hcardG] at h
    omega
  have hn7 : Nat.card (Sylow 7 G) = 1 ∨ Nat.card (Sylow 7 G) = 8 := by
    have hd := Sylow.card_dvd_index P
    rw [hindexP] at hd
    have hm := card_sylow_modEq_one 7 G
    have hp : 0 < Nat.card (Sylow 7 G) := Nat.card_pos
    have hle : Nat.card (Sylow 7 G) ≤ 8 := Nat.le_of_dvd (by norm_num) hd
    simp only [Nat.ModEq] at hm
    omega
  rcases hn7 with hn7 | hn7
  · letI : Subsingleton (Sylow 7 G) := (Nat.card_eq_one_iff_unique.mp hn7).1
    exact ⟨7, P, by norm_num, by norm_num [hG], Sylow.normal_of_subsingleton P⟩
  · have hindexN : (P : Subgroup G).normalizer.index = 8 := by
      rw [← Sylow.card_eq_index_normalizer P]
      exact hn7
    have hcardN : Nat.card (P : Subgroup G).normalizer = 7 := by
      have h := Subgroup.card_mul_index (P : Subgroup G).normalizer
      rw [hindexN, hcardG] at h
      omega
    have hnormalizer : (P : Subgroup G).normalizer = P := by
      apply SetLike.coe_injective
      apply Eq.symm
      apply Set.eq_of_subset_of_card_le
        (show (P : Set G) ⊆ ((P : Subgroup G).normalizer : Set G) from le_normalizer)
      have hc : Nat.card (P : Subgroup G).normalizer ≤ Nat.card (P : Subgroup G) := by
        omega
      simpa only [Nat.card_eq_fintype_card] using hc
    letI : IsCyclic (P : Subgroup G) := isCyclic_of_prime_card hcardP
    have hcentral : (P : Subgroup G).normalizer ≤ Subgroup.centralizer (P : Set G) := by
      rw [hnormalizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val
        (mul_comm (⟨y, hy⟩ : (P : Subgroup G)) (⟨x, hx⟩ : (P : Subgroup G)))
    let f := MonoidHom.transferSylow P hcentral
    let K : Subgroup G := f.ker
    have hcomp : K.IsComplement' P := MonoidHom.ker_transferSylow_isComplement' P hcentral
    have hcardK : Nat.card K = 8 := by
      rw [← hcomp.index_eq_card]
      exact hindexP
    letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    have hpow : Nat.card K = 2 ^ (Nat.card G).factorization 2 := by
      rw [hcardK, hcardG]
      native_decide
    let Q : Sylow 2 G := Sylow.ofCard K hpow
    refine ⟨2, Q, by norm_num, by norm_num [hG], ?_⟩
    change K.Normal
    exact f.normal_ker
