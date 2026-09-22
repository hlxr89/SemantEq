import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] [Fintype G] (hG : Fintype.card G = 56) : ∃ (p : ℕ) (hp : Nat.Prime p) (H : Sylow p G), H.Normal := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_5_13 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 56) :
  ∃ (p : ℕ) (P : Sylow p G), p.Prime ∧ (p ∣ card G) ∧ P.Normal := by
  have hG' : Nat.card G = 56 := by simpa using hG
  let P : Sylow 7 G := default
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hPcard : Nat.card P = 7 := by
    rw [Sylow.card_eq_multiplicity, hG']
    norm_num [show Nat.factorization 56 7 = 1 by native_decide]
  have hPindex : P.index = 8 := by
    have := P.card_mul_index
    rw [hPcard, hG'] at this
    omega
  have hn_dvd : Nat.card (Sylow 7 G) ∣ 8 := by
    simpa [hPindex] using P.card_dvd_index
  have hn_mod : Nat.card (Sylow 7 G) % 7 = 1 := by
    have hm := card_sylow_modEq_one 7 G
    change Nat.card (Sylow 7 G) % 7 = 1 % 7 at hm
    simpa using hm
  have hn : Nat.card (Sylow 7 G) = 1 ∨ Nat.card (Sylow 7 G) = 8 := by
    have hn_le : Nat.card (Sylow 7 G) ≤ 8 := Nat.le_of_dvd (by norm_num) hn_dvd
    have hn_pos : 0 < Nat.card (Sylow 7 G) := Nat.card_pos
    omega
  rcases hn with hn | hn
  · haveI : Subsingleton (Sylow 7 G) := (Nat.card_eq_one_iff_unique.mp hn).1
    exact ⟨7, P, by norm_num, by norm_num [hG], P.normal_of_subsingleton⟩
  · have hNindex : P.normalizer.index = 8 := by
      rw [← P.card_eq_index_normalizer, hn]
    have hrel : P.relIndex P.normalizer = 1 := by
      have := relIndex_mul_index P.le_normalizer
      rw [hPindex, hNindex] at this
      omega
    have hnorm : P.normalizer = P := le_antisymm (relIndex_eq_one.mp hrel) P.le_normalizer
    have hPcyc : IsCyclic P := isCyclic_of_prime_card hPcard
    letI : IsMulCommutative P := ⟨hPcyc.commutative⟩
    have hcent : P.normalizer ≤ Subgroup.centralizer (P : Set G) := by
      rw [hnorm]
      exact P.le_centralizer
    let K : Subgroup G := (MonoidHom.transferSylow P hcent).ker
    have hcomp : K.IsComplement' P := MonoidHom.ker_transferSylow_isComplement' P hcent
    have hKcard : Nat.card K = 8 := by
      have := hcomp.card_mul
      rw [hPcard, hG'] at this
      omega
    let Q : Sylow 2 G := Sylow.ofCard K (by
      rw [hKcard, hG']
      norm_num [show Nat.factorization 56 2 = 3 by native_decide])
    refine ⟨2, Q, by norm_num, by norm_num [hG], ?_⟩
    change K.Normal
    exact (MonoidHom.transferSylow P hcent).normal_ker
