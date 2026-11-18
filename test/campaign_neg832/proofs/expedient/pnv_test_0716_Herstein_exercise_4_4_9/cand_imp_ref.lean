import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} (hp : Fact p.Prime) : (∃ (S : Finset (ZMod p)), S.card = (p - 1) / 2) ∧ (∃ (T : Finset (ZMod p)), T.card = (p - 1) / 2) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4_9 (p : ℕ) (hp : Nat.Prime p) (hodd : p % 2 = 1) :
  (∃ S : Finset (ZMod p), 0 ∉ S ∧ S.card = (p-1)/2 ∧ ∀ q ∈ S, ∃ x : ZMod p, x^2 = q) ∧
  (∃ S : Finset (ZMod p), 0 ∉ S ∧ S.card = (p-1)/2 ∧ ∀ q ∈ S, ¬ ∃ x : ZMod p, x^2 = q) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hchar : ringChar (ZMod p) ≠ 2 := by
    simpa [ZMod.ringChar_zmod_n] using hp2
  let χ := quadraticChar (ZMod p)
  let S : Finset (ZMod p) := Finset.univ.filter fun q => χ q = 1
  let T : Finset (ZMod p) := Finset.univ.filter fun q => χ q = -1
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' hchar
  have hcard : S.card = T.card := by
    apply Finset.card_bij (s := S) (t := T) (fun q _ => (a : ZMod p) * q)
      (fun q hq => ?_) (fun q₁ hq₁ q₂ hq₂ he => ?_)
      (fun q hq => ?_)
    · simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [χ, map_mul, ha]
      simpa [S] using hq
    · exact mul_left_cancel₀ (Units.ne_zero a) he
    · refine ⟨(↑(a⁻¹) : ZMod p) * q, ?_, ?_⟩
      · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        have hainv : quadraticChar (ZMod p) (↑(a⁻¹) : ZMod p) = -1 := by
          rw [← MulChar.coe_toUnitHom]
          rw [MonoidHom.map_inv]
          have hu : (quadraticChar (ZMod p)).toUnitHom a = (-1 : ℤˣ) := by
            apply Units.ext
            exact ha
          rw [hu]
          norm_num
        change quadraticChar (ZMod p) ((↑(a⁻¹) : ZMod p) * q) = 1
        rw [map_mul, hainv]
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hq
        change χ q = -1 at hq
        rw [hq]
        norm_num
      · change (a : ZMod p) * ((↑(a⁻¹) : ZMod p) * q) = q
        rw [← mul_assoc, ← Units.val_mul]
        simp
  have hsum : S.card + T.card = p - 1 := by
    have hST : S ∪ T = Finset.univ.erase 0 := by
      ext q
      simp only [S, T, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_erase]
      by_cases hq : q = 0
      · simp [hq, χ]
      · simpa [χ, hq] using quadraticChar_dichotomy (F := ZMod p) hq
    have hdis : Disjoint S T := by
      rw [Finset.disjoint_left]
      intro q hqS hqT
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hqS
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hqT
      omega
    calc
      S.card + T.card = (S ∪ T).card := (Finset.card_union_of_disjoint hdis).symm
      _ = (Finset.univ.erase (0 : ZMod p)).card := congrArg Finset.card hST
      _ = p - 1 := by simp [ZMod.card]
  have hc : S.card = (p - 1) / 2 := by omega
  have htc : T.card = (p - 1) / 2 := by omega
  refine ⟨⟨S, ?_, hc, ?_⟩, ⟨T, ?_, htc, ?_⟩⟩
  · simp [S, χ]
  · intro q hq
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    have hq0 : q ≠ 0 := by
      intro h
      simp [h, χ] at hq
    have hs : IsSquare q := (quadraticChar_one_iff_isSquare hq0).mp hq
    simpa [isSquare_iff_exists_sq, eq_comm] using hs
  · simp [T, χ]
  · intro q hq
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    rw [quadraticChar_neg_one_iff_not_isSquare] at hq
    simpa [isSquare_iff_exists_sq, eq_comm] using hq
