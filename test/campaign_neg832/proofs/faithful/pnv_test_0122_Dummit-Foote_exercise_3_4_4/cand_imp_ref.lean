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
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
      by_cases hn_one : n = 1
      · subst n
        let T : Subgroup G := ⊥
        letI : Fintype T := inferInstance
        have hTpg : IsPGroup 2 T :=
          IsPGroup.of_card (p := 2) (n := 0) (by simp [T])
        obtain ⟨J, hJ_index⟩ := dummy_assumed hTpg 1 (by simp)
        letI : Fintype J := Fintype.ofFinite J
        let H : Subgroup G := J.map T.subtype
        letI : Fintype H := Fintype.ofFinite H
        refine ⟨H, inferInstance, ?_⟩
        have hJ_card : Nat.card J = 1 := by
          calc
            Nat.card J = 1 * Nat.card J := by simp
            _ = J.index * Nat.card J := by rw [hJ_index]
            _ = Nat.card T := J.index_mul_card
            _ = 1 := by simp [T]
        rw [← Nat.card_eq_fintype_card]
        calc
          Nat.card H = Nat.card J :=
            Subgroup.card_map_of_injective T.subtype_injective
          _ = 1 := hJ_card
      have hn_pos : 0 < n := by
        by_contra hn0
        simp only [not_lt, Nat.le_zero] at hn0
        subst n
        simp at hn
      let p := n.minFac
      have hp_prime : p.Prime := by
        simpa [p] using Nat.minFac_prime hn_one
      letI : Fact p.Prime := ⟨hp_prime⟩
      have hp_dvd_n : p ∣ n := by
        simpa [p] using Nat.minFac_dvd n
      have hp_dvd_G : p ∣ Fintype.card G := hp_dvd_n.trans hn
      let P : Sylow p G := Classical.choice (inferInstance : Nonempty (Sylow p G))
      letI : Fintype P := Fintype.ofFinite P
      have hp_dvd_P : p ∣ Fintype.card P := by
        have hp_dvd_G' : p ∣ Nat.card G := by
          simpa [Nat.card_eq_fintype_card] using hp_dvd_G
        simpa [Nat.card_eq_fintype_card] using P.dvd_card_of_dvd_card hp_dvd_G'
      let d := Fintype.card P / p
      have hd_dvd : d ∣ Fintype.card P := Nat.div_dvd_of_dvd hp_dvd_P
      obtain ⟨K, hK_index⟩ := dummy_assumed P.isPGroup' d hd_dvd
      letI : Fintype K := Fintype.ofFinite K
      let L : Subgroup G := K.map P.1.subtype
      letI : Fintype L := Fintype.ofFinite L
      letI : Fintype (G ⧸ L) := Fintype.ofFinite (G ⧸ L)
      have hd_pos : 0 < d := by
        apply Nat.div_pos (Nat.le_of_dvd Fintype.card_pos hp_dvd_P)
        exact hp_prime.pos
      have hK_card : Fintype.card K = p := by
        apply Nat.eq_of_mul_eq_mul_left hd_pos
        calc
          d * Fintype.card K = K.index * Nat.card K := by
            rw [hK_index, Nat.card_eq_fintype_card]
          _ = Fintype.card P := by
            rw [K.index_mul_card, Nat.card_eq_fintype_card]
          _ = d * p := (Nat.div_mul_cancel hp_dvd_P).symm
      have hL_card : Fintype.card L = p := by
        rw [← hK_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
        exact Subgroup.card_map_of_injective P.1.subtype_injective
      have hn_div_lt : n / p < n := by
        exact Nat.div_lt_self hn_pos hp_prime.one_lt
      have hdiv_dvd_quot : n / p ∣ Fintype.card (G ⧸ L) := by
        obtain ⟨a, ha⟩ := hn
        use a
        have hcardG := L.card_eq_card_quotient_mul_card_subgroup
        have hcardG' : Fintype.card G = Fintype.card (G ⧸ L) * p := by
          simpa only [Nat.card_eq_fintype_card, hL_card] using hcardG
        have hn_eq : n = n / p * p := (Nat.div_mul_cancel hp_dvd_n).symm
        apply Nat.eq_of_mul_eq_mul_right hp_prime.pos
        calc
          Fintype.card (G ⧸ L) * p = Fintype.card G := hcardG'.symm
          _ = n * a := ha
          _ = (n / p * p) * a := congrArg (· * a) hn_eq
          _ = (n / p * a) * p := by ac_rfl
      obtain ⟨Q, Q_fin, hQ_card⟩ :=
        ih (n / p) hn_div_lt (G := G ⧸ L) hdiv_dvd_quot
      letI : Fintype Q := Q_fin
      let C : Subgroup G := Q.comap (QuotientGroup.mk' L)
      letI : Fintype C := Fintype.ofInjective (fun x : C => (x : G)) Subtype.val_injective
      refine ⟨C, inferInstance, ?_⟩
      have hindex : C.index = Q.index := by
        exact Q.index_comap_of_surjective (QuotientGroup.mk'_surjective L)
      have hCeq : Q.index * Fintype.card C = Q.index * (Fintype.card Q * p) := by
        calc
          Q.index * Fintype.card C = C.index * Nat.card C := by
            rw [hindex, Nat.card_eq_fintype_card]
          _ = Fintype.card G := by
            rw [C.index_mul_card, Nat.card_eq_fintype_card]
          _ = Fintype.card (G ⧸ L) * p := by
            simpa only [Nat.card_eq_fintype_card, hL_card] using
              L.card_eq_card_quotient_mul_card_subgroup
          _ = (Q.index * Nat.card Q) * p := by
            rw [Q.index_mul_card, Nat.card_eq_fintype_card]
          _ = Q.index * (Fintype.card Q * p) := by
            rw [Nat.card_eq_fintype_card, Nat.mul_assoc]
      have hQindex_pos : 0 < Q.index := by
        rw [Subgroup.index_eq_card]
        exact Nat.card_pos
      have hC_card : Fintype.card C = Fintype.card Q * p :=
        Nat.eq_of_mul_eq_mul_left hQindex_pos hCeq
      rw [hC_card, hQ_card, Nat.div_mul_cancel hp_dvd_n]
