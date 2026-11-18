import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 56) : ∃ (p : ℕ) (P : Sylow p G), (P : Subgroup G).Normal := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_5_13 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 56) :
  ∃ (p : ℕ) (P : Sylow p G), p.Prime ∧ (p ∣ card G) ∧ P.Normal := by
  have _hdummy := dummy_assumed G hG
  have hcard : Nat.card G = 56 := by simpa using hG
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let P : Sylow 7 G := Classical.choice (show Nonempty (Sylow 7 G) from Sylow.nonempty)
  have hPcard : Nat.card P = 7 := by
    rw [P.card_eq_multiplicity, hcard]
    have hv : padicValNat 7 56 = 1 := by native_decide
    simp [Nat.factorization, hv, show Nat.Prime 7 by norm_num]
  have hPindex : P.index = 8 := by
    have hm := Subgroup.card_mul_index (P : Subgroup G)
    rw [hPcard, hcard] at hm
    omega
  have hn_dvd : Nat.card (Sylow 7 G) ∣ 8 := by
    rw [← hPindex]
    exact P.card_dvd_index
  have hn_mod : Nat.card (Sylow 7 G) ≡ 1 [MOD 7] := card_sylow_modEq_one 7 G
  have hn : Nat.card (Sylow 7 G) = 1 ∨ Nat.card (Sylow 7 G) = 8 := by
    have hn_le : Nat.card (Sylow 7 G) ≤ 8 := Nat.le_of_dvd (by norm_num) hn_dvd
    interval_cases n : Nat.card (Sylow 7 G) <;> simp_all [Nat.ModEq]
  rcases hn with hn | hn
  · letI : Subsingleton (Sylow 7 G) := (Nat.card_eq_one_iff_unique.mp hn).1
    refine ⟨7, P, by norm_num, by simpa [hG], ?_⟩
    exact Sylow.normal_of_subsingleton P
  · have hnorm_index : P.normalizer.index = 8 := by
      rw [← P.card_eq_index_normalizer, hn]
    have hnorm_card : Nat.card P.normalizer = 7 := by
      have hm := Subgroup.card_mul_index P.normalizer
      rw [hnorm_index, hcard] at hm
      omega
    have hnormalizer : P.normalizer = P := by
      symm
      apply Subgroup.eq_of_le_of_card_ge P.le_normalizer
      rw [hnorm_card, hPcard]
    have hcyc : IsCyclic P := isCyclic_of_card_dvd_prime (p := 7) (by simpa [hPcard])
    letI : IsCyclic P := hcyc
    have hcent : P.normalizer ≤ Subgroup.centralizer (P : Set G) := by
      rw [hnormalizer]
      exact P.le_centralizer
    let K : Subgroup G := (MonoidHom.transferSylow P hcent).ker
    have hcomp : K.IsComplement' P := MonoidHom.ker_transferSylow_isComplement' P hcent
    have hKcard : Nat.card K = 8 := by
      have hm := hcomp.card_mul
      rw [hPcard, hcard] at hm
      omega
    have hKp : IsPGroup 2 K := IsPGroup.of_card (p := 2) (n := 3) (by simpa using hKcard)
    letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    let Q : Sylow 2 G := hKp.toSylow (by
      have hi : K.index = 7 := by
        have hm := Subgroup.card_mul_index K
        rw [hKcard, hcard] at hm
        omega
      rw [hi]
      norm_num)
    refine ⟨2, Q, by norm_num, by simpa [hG], ?_⟩
    change K.Normal
    exact inferInstance
