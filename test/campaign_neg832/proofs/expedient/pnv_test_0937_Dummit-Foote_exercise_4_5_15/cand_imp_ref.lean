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
  let P : Sylow 13 G := default
  have hp : Nat.Prime 13 := by norm_num
  letI : Fact (Nat.Prime 13) := ⟨hp⟩
  have hG' : Nat.card G = 351 := by simpa using hG
  have hPcard : Nat.card P = 13 := by
    rw [Sylow.card_eq_multiplicity, Nat.card_eq_fintype_card, hG]
    native_decide
  have hidx : P.index = 27 := by
    have h := P.card_mul_index
    rw [hPcard, Nat.card_eq_fintype_card, hG] at h
    omega
  have hn_dvd : Nat.card (Sylow 13 G) ∣ 27 := by
    simpa [hidx] using P.card_dvd_index
  have hn_mod : Nat.card (Sylow 13 G) ≡ 1 [MOD 13] := card_sylow_modEq_one 13 G
  have hn : Nat.card (Sylow 13 G) = 1 ∨ Nat.card (Sylow 13 G) = 27 := by
    have hnpos : 0 < Nat.card (Sylow 13 G) := Nat.card_pos
    have hnle : Nat.card (Sylow 13 G) ≤ 27 := Nat.le_of_dvd (by omega) hn_dvd
    generalize Nat.card (Sylow 13 G) = n at hnpos hnle hn_mod hn_dvd ⊢
    interval_cases n <;> simp_all [Nat.ModEq]
  rcases hn with hn | hn
  · haveI : Subsingleton (Sylow 13 G) := Fintype.card_le_one_iff_subsingleton.mp (by
      rw [← Nat.card_eq_fintype_card, hn])
    exact ⟨13, P, hp, by norm_num [hG], Sylow.normal_of_subsingleton P⟩
  · have hnormidx : P.normalizer.index = 27 := by
      rw [← P.card_eq_index_normalizer, hn]
    have hnormcard : Nat.card P.normalizer = 13 := by
      have h := P.normalizer.card_mul_index
      rw [hnormidx, hG'] at h
      omega
    have hnorm : P.normalizer = P := by
      apply SetLike.coe_injective
      symm
      apply Set.eq_of_subset_of_ncard_le P.le_normalizer
      simpa using hnormcard.le.trans hPcard.ge
    letI : IsCyclic P := isCyclic_of_prime_card hPcard
    letI : CommGroup P := IsCyclic.commGroup
    have hcent : P.normalizer ≤ Subgroup.centralizer (P : Set G) := by
      intro g hg x hx
      rw [hnorm] at hg
      exact congrArg Subtype.val (mul_comm (⟨g, hg⟩ : P) (⟨x, hx⟩ : P)).symm
    let K : Subgroup G := (MonoidHom.transferSylow P hcent).ker
    have hcomp : IsComplement' K P := MonoidHom.ker_transferSylow_isComplement' P hcent
    have hKcard : Nat.card K = 27 := by
      simpa [K, hidx] using (Subgroup.IsComplement'.index_eq_card hcomp).symm
    let Q : Sylow 3 G := Sylow.ofCard K (by
      rw [hKcard, Nat.card_eq_fintype_card, hG]
      native_decide)
    have hQ : Q.Normal := by
      change K.Normal
      exact inferInstance
    exact ⟨3, Q, by norm_num, by norm_num [hG], hQ⟩
