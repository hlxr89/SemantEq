import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] {n : ℕ} [Fintype G] (hn : Fintype.card G = n) (h : 56 ∣ n) : ∃ (p : ℕ) (hp : p.Prime) (H : Sylow p G), H.Normal := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_5_13 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 56) :
  ∃ (p : ℕ) (P : Sylow p G), p.Prime ∧ (p ∣ card G) ∧ P.Normal := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let P : Sylow 7 G := default
  have hGnat : Nat.card G = 56 := by
    rw [Nat.card_eq_fintype_card, hG]
  have hPcard : Nat.card P = 7 := by
    rw [Sylow.card_eq_multiplicity, hGnat, Nat.factorization_def 56 (by norm_num)]
    rw [show 56 = 2 ^ 3 * 7 ^ 1 by norm_num,
      padicValNat_mul_pow_right (p := 2) (q := 7) 3 1 (by norm_num)]
    norm_num
  have hPindex : P.index = 8 := by
    have h := P.index_mul_card
    rw [hPcard, hGnat] at h
    omega
  have hn_dvd : Nat.card (Sylow 7 G) ∣ 8 := by
    rw [← hPindex]
    exact P.card_dvd_index
  have hn_mod : Nat.card (Sylow 7 G) ≡ 1 [MOD 7] := card_sylow_modEq_one 7 G
  have hn_le : Nat.card (Sylow 7 G) ≤ 8 := Nat.le_of_dvd (by norm_num) hn_dvd
  have hn : Nat.card (Sylow 7 G) = 1 ∨ Nat.card (Sylow 7 G) = 8 := by
    change Nat.card (Sylow 7 G) % 7 = 1 at hn_mod
    omega
  rcases hn with hn | hn
  · letI : Subsingleton (Sylow 7 G) := (Nat.card_eq_one_iff_unique.mp hn).1
    exact ⟨7, P, by norm_num, by rw [hG]; norm_num, Sylow.normal_of_subsingleton P⟩
  · have hNcard : Nat.card P.normalizer = 7 := by
      have h := P.normalizer.index_mul_card
      rw [← P.card_eq_index_normalizer, hn, hGnat] at h
      omega
    have hnorm : P.normalizer = P :=
      (Subgroup.eq_of_le_of_card_ge le_normalizer (by omega)).symm
    have hcyc : IsCyclic P := isCyclic_of_prime_card hPcard
    letI : IsCyclic P := hcyc
    have hcent : P.normalizer ≤ Subgroup.centralizer (P : Set G) := by
      rw [hnorm]
      exact Subgroup.le_centralizer (P : Subgroup G)
    let K := (MonoidHom.transferSylow P hcent).ker
    have hcomp : K.IsComplement' P := MonoidHom.ker_transferSylow_isComplement' P hcent
    have hKcard : Nat.card K = 8 := by
      have h := hcomp.card_mul
      rw [hPcard, hGnat] at h
      omega
    have hKcard' : Nat.card K = 2 ^ (Nat.card G).factorization 2 := by
      rw [hKcard, hGnat, Nat.factorization_def 56 (by norm_num)]
      rw [show 56 = 2 ^ 3 * 7 ^ 1 by norm_num,
        padicValNat_mul_pow_left (p := 2) (q := 7) 3 1 (by norm_num)]
      norm_num
    let Q : Sylow 2 G := Sylow.ofCard K hKcard'
    refine ⟨2, Q, by norm_num, by rw [hG]; norm_num, ?_⟩
    change K.Normal
    infer_instance
