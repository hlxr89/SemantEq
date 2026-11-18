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
  | h m ih =>
      have hm : m ∣ Fintype.card G := by simpa using hn
      by_cases hm1 : m = 1
      · subst m
        exact ⟨⊥, inferInstance, by simp⟩
      have hm0 : m ≠ 0 := by
        intro h0
        subst m
        simpa using (Fintype.card_pos_iff.mpr (inferInstance : Nonempty G)).ne'
          (Nat.eq_zero_of_zero_dvd hm)
      let p := m.minFac
      have hp : p.Prime := Nat.minFac_prime hm1
      have hpm : p ∣ m := Nat.minFac_dvd m
      have hpG : p ∣ Fintype.card G := hpm.trans hm
      letI : Fact p.Prime := ⟨hp⟩
      obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := G) p (n := 1)
        (by simpa [Nat.card_eq_fintype_card] using hpG)
      have hK' : Nat.card K = p := by simpa using hK
      let q := m / p
      have hpq : p * q = m := by
        dsimp [q]
        exact Nat.mul_div_cancel' hpm
      have hq_lt : q < m := by
        exact Nat.div_lt_self (Nat.pos_of_ne_zero hm0) hp.one_lt
      have hquot : Fintype.card (G ⧸ K) * p = Fintype.card G := by
        have ht := K.card_mul_index
        rw [hK', K.index_eq_card] at ht
        simpa [Nat.card_eq_fintype_card, mul_comm] using ht
      obtain ⟨c, hc⟩ := hm
      have hcG : Fintype.card G = m * c := hc
      have hqdiv : q ∣ Fintype.card (G ⧸ K) := by
        refine ⟨c, ?_⟩
        apply Nat.eq_of_mul_eq_mul_right hp.pos
        rw [mul_assoc, hquot, hcG, ← hpq]
        ac_rfl
      obtain ⟨L, L_fin, hL⟩ := ih q hq_lt (G := G ⧸ K) hqdiv
      let H : Subgroup G := L.comap (QuotientGroup.mk' K)
      have hindex : H.index = L.index :=
        L.index_comap_of_surjective (QuotientGroup.mk'_surjective K)
      have hLc : Nat.card L = q := by simpa [Nat.card_eq_fintype_card] using hL
      have hLi : q * L.index = Nat.card (G ⧸ K) := by
        rw [← hLc]
        exact L.card_mul_index
      refine ⟨H, inferInstance, ?_⟩
      have hHi : Nat.card H * H.index = Nat.card G := H.card_mul_index
      have hi_pos : 0 < L.index := by
        rw [L.index_eq_card]
        exact Nat.card_pos
      have hG : Nat.card G = p * Nat.card (G ⧸ K) := by
        simpa [Nat.card_eq_fintype_card, mul_comm] using hquot.symm
      have hHm : Nat.card H = m := by
        apply Nat.eq_of_mul_eq_mul_right hi_pos
        calc
          Nat.card H * L.index = Nat.card H * H.index := congrArg (Nat.card H * ·) hindex.symm
          _ = Nat.card G := hHi
          _ = p * Nat.card (G ⧸ K) := hG
          _ = p * (q * L.index) := by rw [hLi]
          _ = m * L.index := by rw [← mul_assoc, hpq]
      simpa [Nat.card_eq_fintype_card] using hHm
