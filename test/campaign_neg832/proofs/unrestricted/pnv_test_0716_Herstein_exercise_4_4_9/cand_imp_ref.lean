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
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let U : Finset (ZMod p) := Finset.univ.erase 0
  let S : Finset (ZMod p) := U.filter IsSquare
  let T : Finset (ZMod p) := U.filter fun q ↦ ¬ IsSquare q
  have hp2 : p ≠ 2 := by omega
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hchar
  have ha0 : a ≠ 0 := by
    intro ha0
    apply ha
    rw [ha0]
    exact IsSquare.zero
  have hχa : quadraticChar (ZMod p) a = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr ha
  have hχainv : quadraticChar (ZMod p) a⁻¹ = -1 := by
    have hmul : quadraticChar (ZMod p) a * quadraticChar (ZMod p) a⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ ha0, map_one]
    rw [hχa] at hmul
    omega
  have hcard : S.card = T.card := by
    apply Finset.card_bij (fun q _ ↦ a * q)
    · intro q hq
      have hqU : q ∈ U := (Finset.mem_filter.mp hq).1
      have hqs : IsSquare q := (Finset.mem_filter.mp hq).2
      have hq0 : q ≠ 0 := by
        simpa [U] using hqU
      apply Finset.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · simpa [U, ha0, hq0]
      · rw [← quadraticChar_neg_one_iff_not_isSquare]
        rw [map_mul, hχa, (quadraticChar_one_iff_isSquare hq0).mpr hqs]
        norm_num
    · intro q₁ hq₁ q₂ hq₂ heq
      exact (mul_left_cancel₀ ha0 heq)
    · intro q hq
      have hqU : q ∈ U := (Finset.mem_filter.mp hq).1
      have hqn : ¬ IsSquare q := (Finset.mem_filter.mp hq).2
      have hq0 : q ≠ 0 := by
        simpa [U] using hqU
      refine ⟨a⁻¹ * q, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨?_, ?_⟩
        · simpa [U, ha0, hq0]
        · rw [← quadraticChar_one_iff_isSquare (mul_ne_zero (inv_ne_zero ha0) hq0)]
          rw [map_mul, hχainv,
            quadraticChar_neg_one_iff_not_isSquare.mpr hqn]
          norm_num
      · field_simp
  have hpartition : S.card + T.card = p - 1 := by
    calc
      S.card + T.card = U.card := by
        simpa [S, T] using
          (Finset.card_filter_add_card_filter_not (s := U) (p := IsSquare))
      _ = p - 1 := by simp [U, ZMod.card]
  have hScard : S.card = (p - 1) / 2 := by omega
  have hTcard : T.card = (p - 1) / 2 := by omega
  refine ⟨⟨S, ?_, hScard, ?_⟩, ⟨T, ?_, hTcard, ?_⟩⟩
  · simp [S, U]
  · intro q hq
    have hqs : IsSquare q := (Finset.mem_filter.mp hq).2
    simpa [isSquare_iff_exists_sq, eq_comm] using hqs
  · simp [T, U]
  · intro q hq
    have hqn : ¬ IsSquare q := (Finset.mem_filter.mp hq).2
    simpa [isSquare_iff_exists_sq, eq_comm] using hqn
