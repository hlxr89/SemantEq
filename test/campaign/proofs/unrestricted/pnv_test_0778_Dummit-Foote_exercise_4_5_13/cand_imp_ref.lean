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
  let P7 : Sylow 7 G := default
  have hcardP7 : Nat.card P7 = 7 := by
    rw [Sylow.card_eq_multiplicity]
    rw [Nat.card_eq_fintype_card, hG]
    native_decide
  have hindexP7 : P7.index = 8 := by
    have hm := P7.index_mul_card
    rw [hcardP7, Nat.card_eq_fintype_card, hG] at hm
    omega
  have hn7dvd : Nat.card (Sylow 7 G) ∣ 8 := by
    rw [← hindexP7]
    exact P7.card_dvd_index
  have hn7mod : Nat.card (Sylow 7 G) ≡ 1 [MOD 7] := card_sylow_modEq_one 7 G
  have hn7 : Nat.card (Sylow 7 G) = 1 ∨ Nat.card (Sylow 7 G) = 8 := by
    have hn7le : Nat.card (Sylow 7 G) ≤ 8 := Nat.le_of_dvd (by norm_num) hn7dvd
    have hm : Nat.card (Sylow 7 G) % 7 = 1 := by
      simpa [Nat.ModEq] using hn7mod
    omega
  rcases hn7 with hn7 | hn7
  · letI : Subsingleton (Sylow 7 G) :=
      Finite.card_le_one_iff_subsingleton.mp (by omega)
    exact ⟨7, P7, by norm_num, by norm_num [hG], P7.normal_of_subsingleton⟩
  · classical
    have hcard_each7 (P : Sylow 7 G) : Fintype.card P.toSubgroup = 7 := by
      rw [← Nat.card_eq_fintype_card, Sylow.card_eq_multiplicity,
        Nat.card_eq_fintype_card, hG]
      native_decide
    let A := Σ P : Sylow 7 G, {x : P.toSubgroup // x ≠ 1}
    let T := {x : G // orderOf x = 7}
    let f : A → T := fun a => ⟨(a.2.1 : G), by
      have hd : orderOf (a.2.1 : G) ∣ 7 := by
        have hd' := a.1.toSubgroup.orderOf_dvd_natCard a.2.1.2
        simpa [Nat.card_eq_fintype_card, hcard_each7 a.1] using hd'
      have hn : orderOf (a.2.1 : G) ≠ 1 := by
        simpa [orderOf_eq_one_iff] using a.2.2
      exact ((Nat.dvd_prime (by norm_num)).mp hd).resolve_left hn⟩
    have hf_inj : Function.Injective f := by
      rintro ⟨P, x⟩ ⟨Q, y⟩ heq
      have hxy : (x.1 : G) = y.1 := congr_arg Subtype.val heq
      have hxP : (x.1 : G) ∈ (P : Subgroup G) := x.1.2
      have hxQ : (x.1 : G) ∈ (Q : Subgroup G) := hxy ▸ y.1.2
      have hKP : zpowers (x.1 : G) ≤ (P : Subgroup G) := zpowers_le_of_mem hxP
      have hKQ : zpowers (x.1 : G) ≤ (Q : Subgroup G) := zpowers_le_of_mem hxQ
      have hxord : orderOf (x.1 : G) = 7 := (f ⟨P, x⟩).2
      have hKP_eq : zpowers (x.1 : G) = (P : Subgroup G) :=
        Subgroup.eq_of_le_of_card_ge hKP (by
          rw [Nat.card_zpowers, hxord]
          simpa [Nat.card_eq_fintype_card] using (hcard_each7 P).le)
      have hKQ_eq : zpowers (x.1 : G) = (Q : Subgroup G) :=
        Subgroup.eq_of_le_of_card_ge hKQ (by
          rw [Nat.card_zpowers, hxord]
          simpa [Nat.card_eq_fintype_card] using (hcard_each7 Q).le)
      have hPQ : (P : Subgroup G) = Q := hKP_eq.symm.trans hKQ_eq
      have hP : P = Q := Sylow.ext hPQ
      subst Q
      have hxy' : x = y := Subtype.ext (Subtype.ext hxy)
      subst y
      rfl
    have hf_surj : Function.Surjective f := by
      rintro ⟨x, hx⟩
      have hKp : IsPGroup 7 (zpowers x) := by
        rw [IsPGroup.iff_card, Nat.card_zpowers, hx]
        exact ⟨1, by norm_num⟩
      obtain ⟨P, hKP⟩ := hKp.exists_le_sylow
      have hxP : x ∈ (P : Subgroup G) := hKP (Subgroup.mem_zpowers x)
      let xp : P := ⟨x, hxP⟩
      have hxp : xp ≠ 1 := by
        intro he
        have : x = 1 := congr_arg Subtype.val he
        subst x
        simp at hx
      refine ⟨⟨P, ⟨xp, hxp⟩⟩, ?_⟩
      exact Subtype.ext rfl
    have hcardA : Fintype.card A = 48 := by
      simp only [A, Fintype.card_sigma]
      have hfiber (P : Sylow 7 G) :
          Fintype.card {x : P.toSubgroup // x ≠ 1} = 6 := by
        rw [Fintype.card_subtype_compl]
        simp [hcard_each7 P]
      simp_rw [hfiber]
      simp [Nat.card_eq_fintype_card] at hn7
      simp [hn7]
    have hcardT : Fintype.card T = 48 := by
      rw [← hcardA]
      exact (Fintype.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)).symm
    let S := {x : G // orderOf x ≠ 7}
    have hcardS : Fintype.card S = 8 := by
      have hc := Fintype.card_subtype_compl (p := fun x : G => orderOf x = 7)
      change Fintype.card S = Fintype.card G - Fintype.card T at hc
      simpa [hG, hcardT] using hc
    let P2 : Sylow 2 G := default
    have hcardP2 (P : Sylow 2 G) : Fintype.card P.toSubgroup = 8 := by
      rw [← Nat.card_eq_fintype_card, Sylow.card_eq_multiplicity,
        Nat.card_eq_fintype_card, hG]
      native_decide
    have hsub (P : Sylow 2 G) (x : P.toSubgroup) : orderOf (x : G) ≠ 7 := by
      intro hx
      have hd : orderOf x ∣ 8 := by
        rw [← hcardP2 P]
        exact orderOf_dvd_card
      have hcoe : orderOf x = orderOf (x : G) := (Subgroup.orderOf_coe x).symm
      rw [hcoe, hx] at hd
      norm_num at hd
    let e (P : Sylow 2 G) : P.toSubgroup → S := fun x => ⟨x, hsub P x⟩
    have he_bij (P : Sylow 2 G) : Function.Bijective (e P) := by
      apply (Fintype.bijective_iff_injective_and_card (e P)).2
      refine ⟨?_, ?_⟩
      · intro x y hxy
        apply Subtype.ext
        simpa [e] using congr_arg Subtype.val hxy
      · rw [hcardP2 P, hcardS]
    have hsubs : Subsingleton (Sylow 2 G) := ⟨by
      intro P Q
      apply Sylow.ext
      ext x
      constructor
      · intro hx
        obtain ⟨y, hy⟩ := (he_bij Q).2 (e P ⟨x, hx⟩)
        have hv : (y : G) = x := congr_arg Subtype.val hy
        exact hv ▸ y.2
      · intro hx
        obtain ⟨y, hy⟩ := (he_bij P).2 (e Q ⟨x, hx⟩)
        have hv : (y : G) = x := congr_arg Subtype.val hy
        exact hv ▸ y.2⟩
    letI : Subsingleton (Sylow 2 G) := hsubs
    exact ⟨2, P2, by norm_num, by norm_num [hG], P2.normal_of_subsingleton⟩
