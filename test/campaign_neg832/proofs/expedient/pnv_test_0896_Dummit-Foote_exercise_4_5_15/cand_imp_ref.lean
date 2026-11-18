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
  classical
  have hcG : Nat.card G = 351 := by simpa [Nat.card_eq_fintype_card] using hG
  letI : Fact (13 : ℕ).Prime := ⟨by norm_num⟩
  letI : Fact (3 : ℕ).Prime := ⟨by norm_num⟩
  let P13 : Sylow 13 G := Sylow.nonempty.some
  have hc13 (P : Sylow 13 G) : Nat.card P = 13 := by
    rw [Sylow.card_eq_multiplicity, hcG]
    have hv : (351 : ℕ).factorization 13 = 1 := by native_decide
    rw [hv]
    norm_num
  have hn13dvd : Nat.card (Sylow 13 G) ∣ 351 := by
    exact (P13.card_dvd_index).trans (by rw [← hcG]; exact P13.index_dvd_card)
  have hn13mod : Nat.card (Sylow 13 G) ≡ 1 [MOD 13] :=
    card_sylow_modEq_one 13 G
  have hn13 : Nat.card (Sylow 13 G) = 1 ∨ Nat.card (Sylow 13 G) = 27 := by
    have hn13le : Nat.card (Sylow 13 G) ≤ 351 := Nat.le_of_dvd (by norm_num) hn13dvd
    rw [Nat.modEq_iff_dvd] at hn13mod
    interval_cases h : Nat.card (Sylow 13 G)
    all_goals omega
  rcases hn13 with hn13 | hn13
  · have hs : Subsingleton (Sylow 13 G) := (Nat.card_eq_one_iff_unique.mp hn13).1
    letI : Subsingleton (Sylow 13 G) := hs
    refine ⟨13, P13, by norm_num, ?_, Sylow.normal_of_subsingleton P13⟩
    norm_num [hG]
  · let P3 : Sylow 3 G := Sylow.nonempty.some
    have hc3 (P : Sylow 3 G) : Nat.card P = 27 := by
      rw [Sylow.card_eq_multiplicity, hcG]
      have hv : (351 : ℕ).factorization 3 = 3 := by native_decide
      rw [hv]
      norm_num
    have hn3dvd : Nat.card (Sylow 3 G) ∣ 351 := by
      exact (P3.card_dvd_index).trans (by rw [← hcG]; exact P3.index_dvd_card)
    have hn3mod : Nat.card (Sylow 3 G) ≡ 1 [MOD 3] :=
      card_sylow_modEq_one 3 G
    have hn3 : Nat.card (Sylow 3 G) = 1 ∨ Nat.card (Sylow 3 G) = 13 := by
      have hn3le : Nat.card (Sylow 3 G) ≤ 351 := Nat.le_of_dvd (by norm_num) hn3dvd
      rw [Nat.modEq_iff_dvd] at hn3mod
      interval_cases h : Nat.card (Sylow 3 G)
      all_goals omega
    rcases hn3 with hn3 | hn3
    · have hs : Subsingleton (Sylow 3 G) := (Nat.card_eq_one_iff_unique.mp hn3).1
      letI : Subsingleton (Sylow 3 G) := hs
      refine ⟨3, P3, by norm_num, ?_, Sylow.normal_of_subsingleton P3⟩
      norm_num [hG]
    · have hinter13 {P Q : Sylow 13 G} (hne : P ≠ Q) :
          (P : Subgroup G) ⊓ Q = ⊥ := by
        apply (Subgroup.eq_bot_iff_card _).mpr
        have hdvd : Nat.card ↥((P : Subgroup G) ⊓ Q) ∣ 13 := by
          have hd := (((P : Subgroup G) ⊓ Q).subgroupOf P).card_subgroup_dvd_card
          have hequiv :
              ↥(((P : Subgroup G) ⊓ Q).subgroupOf P) ≃ ↥((P : Subgroup G) ⊓ Q) :=
            (Subgroup.subgroupOfEquivOfLe
              (show (P : Subgroup G) ⊓ Q ≤ P from inf_le_left)).toEquiv
          have heq := Nat.card_congr hequiv
          have hd' : Nat.card ↥((P : Subgroup G) ⊓ Q) ∣ Nat.card ↥(P : Subgroup G) := by
            rw [← heq]
            exact hd
          simpa only [hc13 P] using hd'
        rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h | h
        · exact h
        · exfalso
          apply hne
          apply Sylow.ext
          have hiP : (P : Subgroup G) ⊓ Q = P :=
            Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hc13])
          have hiQ : (P : Subgroup G) ⊓ Q = Q :=
            Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hc13])
          exact hiP.symm.trans hiQ
      let S13 (P : Sylow 13 G) : Finset G :=
        (Finset.univ.map ⟨fun x : (P : Subgroup G) ↦ x.1, Subtype.coe_injective⟩).erase 1
      let U13 : Finset G := Finset.univ.biUnion S13
      have hcardS13 (P : Sylow 13 G) : (S13 P).card = 12 := by
        rw [Finset.card_erase_of_mem]
        · simp [S13, ← Nat.card_eq_fintype_card, hc13]
        · simp [S13]
      have hdisj13 : ((Finset.univ : Finset (Sylow 13 G)) : Set (Sylow 13 G)).PairwiseDisjoint S13 := by
        intro P _ Q _ hne
        change Disjoint (S13 P) (S13 Q)
        rw [Finset.disjoint_left]
        intro x hxP hxQ
        have hxP' : x ≠ 1 ∧ x ∈ (P : Subgroup G) := by simpa [S13] using hxP
        have hxQ' : x ≠ 1 ∧ x ∈ (Q : Subgroup G) := by simpa [S13] using hxQ
        have hxinf : x ∈ (P : Subgroup G) ⊓ Q := ⟨hxP'.2, hxQ'.2⟩
        rw [hinter13 hne] at hxinf
        exact hxP'.1 (by simpa using hxinf)
      have hcardU13 : U13.card = 324 := by
        rw [show U13 = Finset.univ.biUnion S13 from rfl, Finset.card_biUnion hdisj13]
        simp [hcardS13]
        rw [← Nat.card_eq_fintype_card, hn13]
      have hinter3_13 (P : Sylow 3 G) (Q : Sylow 13 G) :
          (P : Subgroup G) ⊓ Q = ⊥ := by
        apply (Subgroup.eq_bot_iff_card _).mpr
        have hdvd27 : Nat.card ↥((P : Subgroup G) ⊓ Q) ∣ 27 := by
          have hd := (((P : Subgroup G) ⊓ Q).subgroupOf P).card_subgroup_dvd_card
          have hequiv :
              ↥(((P : Subgroup G) ⊓ Q).subgroupOf P) ≃ ↥((P : Subgroup G) ⊓ Q) :=
            (Subgroup.subgroupOfEquivOfLe
              (show (P : Subgroup G) ⊓ Q ≤ P from inf_le_left)).toEquiv
          have heq := Nat.card_congr hequiv
          have hd' : Nat.card ↥((P : Subgroup G) ⊓ Q) ∣ Nat.card ↥(P : Subgroup G) := by
            rw [← heq]
            exact hd
          simpa only [hc3 P] using hd'
        have hdvd13 : Nat.card ↥((P : Subgroup G) ⊓ Q) ∣ 13 := by
          have hd := (((P : Subgroup G) ⊓ Q).subgroupOf Q).card_subgroup_dvd_card
          have hequiv :
              ↥(((P : Subgroup G) ⊓ Q).subgroupOf Q) ≃ ↥((P : Subgroup G) ⊓ Q) :=
            (Subgroup.subgroupOfEquivOfLe
              (show (P : Subgroup G) ⊓ Q ≤ Q from inf_le_right)).toEquiv
          have heq := Nat.card_congr hequiv
          have hd' : Nat.card ↥((P : Subgroup G) ⊓ Q) ∣ Nat.card ↥(Q : Subgroup G) := by
            rw [← heq]
            exact hd
          simpa only [hc13 Q] using hd'
        have hd := Nat.dvd_gcd hdvd27 hdvd13
        norm_num at hd
        rw [Nat.card_eq_fintype_card]
        simpa only [Subgroup.mem_inf] using hd
      let S3 (P : Sylow 3 G) : Finset G :=
        (Finset.univ.map ⟨fun x : (P : Subgroup G) ↦ x.1, Subtype.coe_injective⟩).erase 1
      let All : Finset G := Finset.univ.erase 1
      have hcardS3 (P : Sylow 3 G) : (S3 P).card = 26 := by
        rw [Finset.card_erase_of_mem]
        · simp [S3, ← Nat.card_eq_fintype_card, hc3]
        · simp [S3]
      have hdisj3U (P : Sylow 3 G) : Disjoint (S3 P) U13 := by
        rw [Finset.disjoint_left]
        intro x hx3 hxU
        rw [show U13 = Finset.univ.biUnion S13 from rfl, Finset.mem_biUnion] at hxU
        obtain ⟨Q, _, hx13⟩ := hxU
        have hx3' : x ≠ 1 ∧ x ∈ (P : Subgroup G) := by simpa [S3] using hx3
        have hx13' : x ≠ 1 ∧ x ∈ (Q : Subgroup G) := by simpa [S13] using hx13
        have hxinf : x ∈ (P : Subgroup G) ⊓ Q := ⟨hx3'.2, hx13'.2⟩
        rw [hinter3_13 P Q] at hxinf
        exact hx3'.1 (by simpa using hxinf)
      have hUsub : U13 ⊆ All := by
        intro x hx
        rw [show U13 = Finset.univ.biUnion S13 from rfl, Finset.mem_biUnion] at hx
        obtain ⟨Q, _, hxQ⟩ := hx
        have hxQ' : x ≠ 1 ∧ x ∈ (Q : Subgroup G) := by simpa [S13] using hxQ
        simp [All, hxQ'.1]
      have hcardAll : All.card = 350 := by
        simp [All, hG]
      have hcardDiff : (All \ U13).card = 26 := by
        rw [Finset.card_sdiff_of_subset hUsub, hcardAll, hcardU13]
      have hS3eq (P : Sylow 3 G) : S3 P = All \ U13 := by
        apply Finset.eq_of_subset_of_card_le
        · exact Finset.subset_sdiff.mpr ⟨by intro x hx; simp [All, S3] at hx ⊢; exact hx.1,
            hdisj3U P⟩
        · rw [hcardDiff, hcardS3]
      have hs : Subsingleton (Sylow 3 G) := ⟨by
        intro P Q
        apply Sylow.ext
        ext x
        by_cases hx : x = 1
        · simp [hx]
        · have heq : S3 P = S3 Q := (hS3eq P).trans (hS3eq Q).symm
          have hm := Finset.ext_iff.mp heq x
          simpa [S3, hx] using hm⟩
      letI : Subsingleton (Sylow 3 G) := hs
      refine ⟨3, P3, by norm_num, ?_, Sylow.normal_of_subsingleton P3⟩
      norm_num [hG]
