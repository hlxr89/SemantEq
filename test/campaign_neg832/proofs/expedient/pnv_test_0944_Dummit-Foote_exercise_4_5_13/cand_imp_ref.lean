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
  have hG' : Nat.card G = 56 := by simpa using hG
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let P : Sylow 7 G := default
  let n := Fintype.card (Sylow 7 G)
  have hn_dvd : n ∣ 56 := by
    rw [← hG]
    simpa [n] using (P.card_dvd_index).trans P.1.index_dvd_card
  have hn_mod : n ≡ 1 [MOD 7] := by simpa [n] using card_sylow_modEq_one 7 G
  have hn : n = 1 ∨ n = 8 := by
    have hn_le : n ≤ 56 := Nat.le_of_dvd (by norm_num) hn_dvd
    interval_cases n <;> norm_num at hn_dvd <;> norm_num [Nat.ModEq] at hn_mod <;> omega
  rcases hn with hn | hn
  · haveI : Subsingleton (Sylow 7 G) := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    exact ⟨7, P, by norm_num, by omega, Sylow.normal_of_subsingleton P⟩
  · have hPcard : Nat.card P = 7 := by
      rw [P.card_eq_multiplicity, hG']
      native_decide
    have hPindex : P.1.index = 8 := by
      have h := P.1.card_mul_index
      rw [hPcard, hG'] at h
      omega
    have hNindex : P.normalizer.index = 8 := by
      rw [← P.card_eq_index_normalizer]
      simpa [n] using hn
    have hPN : P.1 = P.normalizer := by
      apply le_antisymm P.le_normalizer
      apply Subgroup.relIndex_eq_one.mp
      have h := Subgroup.relIndex_mul_index P.le_normalizer
      rw [hNindex, hPindex] at h
      omega
    have hPcyc : IsCyclic P := isCyclic_of_prime_card hPcard
    letI : IsCyclic P := hPcyc
    have hcentral : P.normalizer ≤ Subgroup.centralizer (P : Set G) := by
      rw [← hPN]
      intro x hx y hy
      simpa using congr_arg Subtype.val
        (IsCyclic.commutative.comm (⟨y, hy⟩ : P) (⟨x, hx⟩ : P))
    let K : Subgroup G := (MonoidHom.transferSylow P hcentral).ker
    have hcomp : K.IsComplement' P := MonoidHom.ker_transferSylow_isComplement' P hcentral
    have hKcard : Nat.card K = 8 := by
      have hKi : K.index = 7 := by simpa [hPcard] using hcomp.symm.index_eq_card
      have h := K.card_mul_index
      rw [hKi, hG'] at h
      omega
    haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    let Q : Sylow 2 G := Sylow.ofCard K (by
      rw [hG']
      rw [hKcard]
      native_decide)
    refine ⟨2, Q, by norm_num, by omega, ?_⟩
    change K.Normal
    infer_instance
