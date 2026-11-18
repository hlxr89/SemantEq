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
  obtain ⟨⟨A, hA⟩, ⟨B, hB⟩⟩ := dummy_assumed (p := p) (inferInstanceAs (Fact p.Prime))
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    norm_num at hodd
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  obtain ⟨a, haχ⟩ := quadraticChar_exists_neg_one (F := ZMod p) hchar
  have ha : a ≠ 0 := by
    intro ha
    subst a
    simp at haχ
  let S : Finset (ZMod p) := Finset.univ.filter fun q => quadraticChar (ZMod p) q = 1
  let T : Finset (ZMod p) := Finset.univ.filter fun q => quadraticChar (ZMod p) q = -1
  let e : Equiv.Perm (ZMod p) := Equiv.mulLeft₀ a ha
  have hST : S.card = T.card := by
    apply Finset.card_bij (fun q _ => e q)
    · intro q hq
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      change quadraticChar (ZMod p) (a * q) = -1
      rw [map_mul, haχ, hq]
      norm_num
    · intro q₁ hq₁ q₂ hq₂ heq
      exact e.injective heq
    · intro q hq
      refine ⟨e.symm q, ?_, e.apply_symm_apply q⟩
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      have heq : a * e.symm q = q := e.apply_symm_apply q
      have hmap := congrArg (quadraticChar (ZMod p)) heq
      rw [map_mul, haχ, hq] at hmap
      omega
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro q hqS hqT
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hqS
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hqT
    omega
  have hunion : S ∪ T = Finset.univ.erase 0 := by
    ext q
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_univ, and_true]
    simp only [S, T, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (hq | hq) rfl <;> simp at hq
    · intro hq
      exact quadraticChar_dichotomy hq
  have hsum : S.card + T.card = p - 1 := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_erase_of_mem]
    · simp [ZMod.card]
    · simp
  have hScardA : S.card = A.card := by
    rw [hA]
    omega
  have hTcardB : T.card = B.card := by
    rw [hB]
    omega
  have hScard : S.card = (p - 1) / 2 := hScardA.trans hA
  have hTcard : T.card = (p - 1) / 2 := hTcardB.trans hB
  constructor
  · refine ⟨S, ?_, hScard, ?_⟩
    · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      simp
    · intro q hq
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      have hq0 : q ≠ 0 := by
        intro h
        subst q
        simp at hq
      have hsq : IsSquare q := (quadraticChar_one_iff_isSquare hq0).mp hq
      rcases hsq with ⟨x, hx⟩
      exact ⟨x, by simpa [pow_two] using hx.symm⟩
  · refine ⟨T, ?_, hTcard, ?_⟩
    · simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      simp
    · intro q hq
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      have hnonsq : ¬IsSquare q := quadraticChar_neg_one_iff_not_isSquare.mp hq
      rintro ⟨x, hx⟩
      apply hnonsq
      exact ⟨x, by simpa [pow_two] using hx.symm⟩
