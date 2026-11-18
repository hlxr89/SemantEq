import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (G : Type*) [Group G] [Finite G] : ∃ (p : Nat) (hp : p.Prime) (P : Sylow p G), (P : Subgroup G).Normal := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_5_15 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 351) :
  ∃ (p : ℕ) (P : Sylow p G), p.Prime ∧ (p ∣ card G) ∧  P.Normal := by
  have hGnat : Nat.card G = 351 := by
    rw [Nat.card_eq_fintype_card]
    exact hG
  have hf13 : Nat.factorization 351 13 = 1 := by
    rw [show 351 = 13 * 27 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 13 ∣ 27)]
  have hf3 : Nat.factorization 351 3 = 3 := by
    rw [show 351 = 27 * 13 by norm_num,
      show 27 = 3 ^ 3 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 13)]
  letI : Fact (13 : ℕ).Prime := ⟨by norm_num⟩
  let P : Sylow 13 G := default
  have hPcard : Nat.card P = 13 := by
    rw [P.card_eq_multiplicity, hGnat]
    simp [hf13]
  have hPindex : (P : Subgroup G).index = 27 := by
    have h := index_mul_card (P : Subgroup G)
    rw [hPcard, hGnat] at h
    omega
  have hn_dvd : Nat.card (Sylow 13 G) ∣ 27 := by
    simpa [hPindex] using P.card_dvd_index
  have hn_mod : Nat.card (Sylow 13 G) ≡ 1 [MOD 13] := card_sylow_modEq_one 13 G
  have hn_cases : Nat.card (Sylow 13 G) = 1 ∨ Nat.card (Sylow 13 G) = 27 := by
    rw [Nat.card_eq_fintype_card]
    have hn_dvdF : Fintype.card (Sylow 13 G) ∣ 27 := by
      simpa only [Nat.card_eq_fintype_card] using hn_dvd
    have hn_modF : Fintype.card (Sylow 13 G) ≡ 1 [MOD 13] := by
      simpa only [Nat.card_eq_fintype_card] using hn_mod
    have hn_dvd' : Fintype.card (Sylow 13 G) ∣ 3 ^ 3 := hn_dvdF
    obtain ⟨k, hk, hcard⟩ :=
      (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hn_dvd'
    interval_cases k
    all_goals norm_num at hcard
    all_goals rw [hcard] at hn_modF ⊢
    all_goals first | exact Or.inl rfl | exact Or.inr rfl | norm_num [Nat.ModEq] at hn_modF
  rcases hn_cases with hn | hn
  · haveI : Subsingleton (Sylow 13 G) :=
      (Nat.card_eq_one_iff_unique.mp hn).1
    refine ⟨13, P, by norm_num, by norm_num [hG], ?_⟩
    exact P.normal_of_subsingleton
  · have hNindex : P.normalizer.index = 27 := by
      rw [← P.card_eq_index_normalizer]
      exact hn
    have hrel : P.relIndex P.normalizer = 1 := by
      have h := relIndex_mul_index P.le_normalizer
      rw [hNindex, hPindex] at h
      omega
    have hnormalizer : P.normalizer = P := by
      exact (relIndex_eq_one.mp hrel).antisymm P.le_normalizer
    have hcyclic : IsCyclic P := isCyclic_of_prime_card hPcard
    letI : IsCyclic P := hcyclic
    letI : CommGroup P := IsCyclic.commGroup
    letI : IsMulCommutative P := ⟨⟨fun a b ↦ mul_comm a b⟩⟩
    have hcentral : P.normalizer ≤ Subgroup.centralizer (P : Set G) := by
      rw [hnormalizer]
      exact Subgroup.le_centralizer (P : Subgroup G)
    let K : Subgroup G := (MonoidHom.transferSylow P hcentral).ker
    have hcomp : K.IsComplement' P :=
      MonoidHom.ker_transferSylow_isComplement' P hcentral
    have hKcard : Nat.card K = 27 := by
      have h := hcomp.index_eq_card
      rw [hPindex] at h
      exact h.symm
    let Q : Sylow 3 G := Sylow.ofCard K (by
      rw [hKcard, hGnat]
      simp [hf3])
    refine ⟨3, Q, by norm_num, by norm_num [hG], ?_⟩
    exact MonoidHom.normal_ker _
