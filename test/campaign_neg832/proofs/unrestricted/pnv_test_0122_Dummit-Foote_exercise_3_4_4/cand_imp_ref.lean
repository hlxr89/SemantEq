import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed [Fintype G] [CommGroup G] (hp : IsPGroup p G): ∀ (d : ℕ), d ∣ Fintype.card G → ∃ H : Subgroup G, H.index = d := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_4_4 {G : Type*} [CommGroup G] [Fintype G] {n : ℕ}
    (hn : n ∣ (card G)) :
    ∃ (H : Subgroup G) (H_fin : Fintype H), @card H H_fin = n  := by
  classical
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
    rcases n with _ | n
    · have hzero : Fintype.card G = 0 := by simpa using hn
      exact (Fintype.card_ne_zero hzero).elim
    rcases n with _ | n
    · let H : Subgroup G := ⊥
      let H_fin : Fintype H := Fintype.ofFinite H
      refine ⟨H, H_fin, ?_⟩
      simp [H]
    · let N := n + 2
      have hN : N ≠ 1 := by omega
      obtain ⟨p, hp, hpN⟩ := Nat.exists_prime_and_dvd hN
      letI : Fact p.Prime := ⟨hp⟩
      have hpG : p ∣ Fintype.card G := hpN.trans hn
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card p hpG
      let K : Subgroup G := Subgroup.zpowers x
      have hKcard : Nat.card K = p := by
        change Nat.card (Subgroup.zpowers x) = p
        rw [Nat.card_zpowers, hx]
      have hGcard : Fintype.card G = Nat.card (G ⧸ K) * p := by
        rw [← Nat.card_eq_fintype_card, K.card_eq_card_quotient_mul_card_subgroup,
          hKcard]
      have hquot_dvd : N / p ∣ Nat.card (G ⧸ K) := by
        apply Nat.dvd_of_mul_dvd_mul_right hp.pos
        rw [Nat.div_mul_cancel hpN]
        simpa only [hGcard] using hn
      have hlt : N / p < N := Nat.div_lt_self (by omega) hp.one_lt
      letI : Fintype (G ⧸ K) := Fintype.ofFinite (G ⧸ K)
      have hquot_dvd' : N / p ∣ Fintype.card (G ⧸ K) := by
        simpa only [← Nat.card_eq_fintype_card] using hquot_dvd
      obtain ⟨Q, Q_fin, hQcard⟩ := ih (N / p) hlt (G := G ⧸ K) hquot_dvd'
      let q : G →* G ⧸ K := QuotientGroup.mk' K
      let H : Subgroup G := Q.comap q
      let H_fin : Fintype H := Fintype.ofFinite H
      refine ⟨H, H_fin, ?_⟩
      have hindex : H.index = Q.index := by
        exact Q.index_comap_of_surjective (QuotientGroup.mk'_surjective K)
      have hQmul : (N / p) * Q.index = Nat.card (G ⧸ K) := by
        rw [← hQcard]
        simpa only [Nat.card_eq_fintype_card] using Q.card_mul_index
      have hHmul : Nat.card H * Q.index = Fintype.card G := by
        rw [← hindex]
        simpa only [Nat.card_eq_fintype_card] using H.card_mul_index
      have hmul : Nat.card H * Q.index = N * Q.index := by
        calc
          Nat.card H * Q.index = Fintype.card G := hHmul
          _ = Nat.card (G ⧸ K) * p := hGcard
          _ = ((N / p) * Q.index) * p := by rw [hQmul]
          _ = ((N / p) * p) * Q.index := by ac_rfl
          _ = N * Q.index := by rw [Nat.div_mul_cancel hpN]
      have hHcard : Nat.card H = N :=
        Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero Q.index_ne_zero_of_finite) hmul
      rw [← Nat.card_eq_fintype_card]
      exact hHcard
