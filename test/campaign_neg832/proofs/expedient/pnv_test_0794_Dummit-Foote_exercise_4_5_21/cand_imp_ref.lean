import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] (h : Nat.card G = 2907) : ∃ H : Subgroup G, H.Normal ∧ H ≠ ⊥ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_5_21 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 2907) : ¬ IsSimpleGroup G := by
  letI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  have hG' : Nat.card G = 2907 := by
    simpa [Nat.card_eq_fintype_card] using hG
  have hp17 (P : Sylow 17 G) : Nat.card P = 17 := by
    rw [Sylow.card_eq_multiplicity, hG']
    native_decide
  have hp19 (P : Sylow 19 G) : Nat.card P = 19 := by
    rw [Sylow.card_eq_multiplicity, hG']
    native_decide
  intro hs
  have hn17 : Nat.card (Sylow 17 G) = 171 := by
    have hd : Nat.card (Sylow 17 G) ∣ 171 := by
      let P : Sylow 17 G := default
      have hi : P.index = 171 := by
        have hm := P.card_mul_index
        rw [hp17 P, hG'] at hm
        omega
      rw [← hi]
      exact Sylow.card_dvd_index P
    have hm := card_sylow_modEq_one 17 G
    have hle := Nat.le_of_dvd (by norm_num : 0 < 171) hd
    have hor : Nat.card (Sylow 17 G) = 1 ∨ Nat.card (Sylow 17 G) = 171 := by
      exact (show ∀ n : Fin 172, n.val ≡ 1 [MOD 17] → n.val ∣ 171 →
          n.val = 1 ∨ n.val = 171 by native_decide)
        ⟨Nat.card (Sylow 17 G), Nat.lt_succ_iff.mpr hle⟩ hm hd
    rcases hor with hone | hmax
    · letI : Subsingleton (Sylow 17 G) := (Nat.card_eq_one_iff_unique.mp hone).1
      let P : Sylow 17 G := default
      have hn := Sylow.normal_of_subsingleton P
      rcases hs.eq_bot_or_eq_top_of_normal (P : Subgroup G) hn with hb | ht
      · have hp := hp17 P
        rw [hb, card_bot] at hp
        norm_num at hp
      · have hp := hp17 P
        rw [ht, card_top, hG'] at hp
        norm_num at hp
    · exact hmax
  have hn19 : Nat.card (Sylow 19 G) = 153 := by
    have hd : Nat.card (Sylow 19 G) ∣ 153 := by
      let P : Sylow 19 G := default
      have hi : P.index = 153 := by
        have hm := P.card_mul_index
        rw [hp19 P, hG'] at hm
        omega
      rw [← hi]
      exact Sylow.card_dvd_index P
    have hm := card_sylow_modEq_one 19 G
    have hle := Nat.le_of_dvd (by norm_num : 0 < 153) hd
    have hor : Nat.card (Sylow 19 G) = 1 ∨ Nat.card (Sylow 19 G) = 153 := by
      exact (show ∀ n : Fin 154, n.val ≡ 1 [MOD 19] → n.val ∣ 153 →
          n.val = 1 ∨ n.val = 153 by native_decide)
        ⟨Nat.card (Sylow 19 G), Nat.lt_succ_iff.mpr hle⟩ hm hd
    rcases hor with hone | hmax
    · letI : Subsingleton (Sylow 19 G) := (Nat.card_eq_one_iff_unique.mp hone).1
      let P : Sylow 19 G := default
      have hn := Sylow.normal_of_subsingleton P
      rcases hs.eq_bot_or_eq_top_of_normal (P : Subgroup G) hn with hb | ht
      · have hp := hp19 P
        rw [hb, card_bot] at hp
        norm_num at hp
      · have hp := hp19 P
        rw [ht, card_top, hG'] at hp
        norm_num at hp
    · exact hmax
  let A17 := Σ P : Sylow 17 G, {x : (P : Subgroup G) // x ≠ 1}
  let A19 := Σ P : Sylow 19 G, {x : (P : Subgroup G) // x ≠ 1}
  have order17 (P : Sylow 17 G) (x : G) (hxP : x ∈ P) (hx1 : x ≠ 1) :
      orderOf x = 17 := by
    have hd' := orderOf_dvd_natCard (⟨x, hxP⟩ : (P : Subgroup G))
    rw [← Subgroup.orderOf_coe, hp17 P] at hd'
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 17)).mp hd' with h | h
    · exact (hx1 (orderOf_eq_one_iff.mp h)).elim
    · exact h
  have order19 (P : Sylow 19 G) (x : G) (hxP : x ∈ P) (hx1 : x ≠ 1) :
      orderOf x = 19 := by
    have hd' := orderOf_dvd_natCard (⟨x, hxP⟩ : (P : Subgroup G))
    rw [← Subgroup.orderOf_coe, hp19 P] at hd'
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 19)).mp hd' with h | h
    · exact (hx1 (orderOf_eq_one_iff.mp h)).elim
    · exact h
  have unique17 (P Q : Sylow 17 G) (x : G) (hxP : x ∈ P) (hxQ : x ∈ Q)
      (hx1 : x ≠ 1) : P = Q := by
    have ho := order17 P x hxP hx1
    apply Sylow.ext
    have hQ : zpowers x = (Q : Subgroup G) := by
      apply Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hxQ)
      rw [Nat.card_zpowers, ho, hp17 Q]
    have hP : zpowers x = (P : Subgroup G) := by
      apply Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hxP)
      rw [Nat.card_zpowers, ho, hp17 P]
    exact hP.symm.trans hQ
  have unique19 (P Q : Sylow 19 G) (x : G) (hxP : x ∈ P) (hxQ : x ∈ Q)
      (hx1 : x ≠ 1) : P = Q := by
    have ho := order19 P x hxP hx1
    apply Sylow.ext
    have hQ : zpowers x = (Q : Subgroup G) := by
      apply Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hxQ)
      rw [Nat.card_zpowers, ho, hp19 Q]
    have hP : zpowers x = (P : Subgroup G) := by
      apply Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hxP)
      rw [Nat.card_zpowers, ho, hp19 P]
    exact hP.symm.trans hQ
  let f : A17 ⊕ A19 → {x : G // x ≠ 1}
    | Sum.inl a => ⟨a.2.1.1, fun h => a.2.2 (Subtype.ext h)⟩
    | Sum.inr a => ⟨a.2.1.1, fun h => a.2.2 (Subtype.ext h)⟩
  have hf : Function.Injective f := by
    rintro (⟨P, x⟩ | ⟨P, x⟩) (⟨Q, y⟩ | ⟨Q, y⟩) h
    · have hxy : (x.1 : G) = y.1 := congrArg Subtype.val h
      have hPQ := unique17 P Q x.1 x.1.2 (hxy ▸ y.1.2) (fun hx => x.2 (Subtype.ext hx))
      subst Q
      congr
      exact Subtype.ext (Subtype.ext hxy)
    · have hxy : (x.1 : G) = y.1 := congrArg Subtype.val h
      have hx := order17 P x.1 x.1.2 (fun hx => x.2 (Subtype.ext hx))
      have hy := order19 Q y.1 y.1.2 (fun hy => y.2 (Subtype.ext hy))
      rw [hxy] at hx
      norm_num [hx] at hy
    · have hxy : (x.1 : G) = y.1 := congrArg Subtype.val h
      have hx := order19 P x.1 x.1.2 (fun hx => x.2 (Subtype.ext hx))
      have hy := order17 Q y.1 y.1.2 (fun hy => y.2 (Subtype.ext hy))
      rw [hxy] at hx
      norm_num [hx] at hy
    · have hxy : (x.1 : G) = y.1 := congrArg Subtype.val h
      have hPQ := unique19 P Q x.1 x.1.2 (hxy ▸ y.1.2) (fun hx => x.2 (Subtype.ext hx))
      subst Q
      congr
      exact Subtype.ext (Subtype.ext hxy)
  have hc17 : Nat.card A17 = 171 * 16 := by
    dsimp [A17]
    letI (P : Sylow 17 G) := Fintype.ofFinite (P : Subgroup G)
    letI (P : Sylow 17 G) := Fintype.ofFinite {x : (P : Subgroup G) // x ≠ 1}
    letI := Fintype.ofFinite (Sylow 17 G)
    have hi (P : Sylow 17 G) : Nat.card {x : (P : Subgroup G) // x ≠ 1} = 16 := by
      rw [Nat.card_eq_fintype_card,
        Fintype.card_subtype_compl (fun x : (P : Subgroup G) => x = 1)]
      simp [← Nat.card_eq_fintype_card, hp17 P]
    rw [Nat.card_sigma]
    simp only [hi, Finset.sum_const, nsmul_eq_mul]
    rw [Finset.card_univ]
    norm_num [Nat.card_eq_fintype_card] at hn17 ⊢
    rw [hn17]
    norm_num
  have hc19 : Nat.card A19 = 153 * 18 := by
    dsimp [A19]
    letI (P : Sylow 19 G) := Fintype.ofFinite (P : Subgroup G)
    letI (P : Sylow 19 G) := Fintype.ofFinite {x : (P : Subgroup G) // x ≠ 1}
    letI := Fintype.ofFinite (Sylow 19 G)
    have hi (P : Sylow 19 G) : Nat.card {x : (P : Subgroup G) // x ≠ 1} = 18 := by
      rw [Nat.card_eq_fintype_card,
        Fintype.card_subtype_compl (fun x : (P : Subgroup G) => x = 1)]
      simp [← Nat.card_eq_fintype_card, hp19 P]
    rw [Nat.card_sigma]
    simp only [hi, Finset.sum_const, nsmul_eq_mul]
    rw [Finset.card_univ]
    norm_num [Nat.card_eq_fintype_card] at hn19 ⊢
    rw [hn19]
    norm_num
  have hle := Nat.card_le_card_of_injective f hf
  rw [Nat.card_sum, hc17, hc19] at hle
  letI := Fintype.ofFinite {x : G // x ≠ 1}
  have htarget : Nat.card {x : G // x ≠ 1} = 2906 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun x : G => x = 1)]
    simp [← Nat.card_eq_fintype_card, hG']
  rw [htarget] at hle
  norm_num at hle
