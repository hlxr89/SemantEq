import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (p : ℕ) [Fact p.Prime] : (∃ n, n = (p - 1) / 2 ∧ (∃ (quadratic_residues : Finset (ZMod p)) (quadratic_nonresidues : Finset (ZMod p)), quadratic_residues.card = n ∧ quadratic_nonresidues.card = n ∧ ∀ x : ZMod p, x ≠ 0 → (x ∈ quadratic_residues ∨ x ∈ quadratic_nonresidues) ∧ (x ∈ quadratic_residues ↔ ¬ (x ∈ quadratic_nonresidues)))) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4_9 (p : ℕ) (hp : Nat.Prime p) (hodd : p % 2 = 1) :
  (∃ S : Finset (ZMod p), 0 ∉ S ∧ S.card = (p-1)/2 ∧ ∀ q ∈ S, ∃ x : ZMod p, x^2 = q) ∧
  (∃ S : Finset (ZMod p), 0 ∉ S ∧ S.card = (p-1)/2 ∧ ∀ q ∈ S, ¬ ∃ x : ZMod p, x^2 = q) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hc : ringChar (ZMod p) ≠ 2 := (ZMod.ringChar_zmod_n p).substr hp2
  let R : Finset (ZMod p) := Finset.univ.filter fun q => quadraticChar (ZMod p) q = 1
  let N : Finset (ZMod p) := Finset.univ.filter fun q => quadraticChar (ZMod p) q = -1
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one hc
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, quadraticChar_zero] at ha
    norm_num at ha
  have hcard : R.card = N.card := by
    apply Finset.card_bij' (fun q _ => a * q) (fun q _ => a⁻¹ * q)
    · intro q hq
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      dsimp [N]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change quadraticChar (ZMod p) (a * q) = -1
      rw [map_mul, ha, hq]
      norm_num
    · intro q hq
      simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      dsimp [R]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change quadraticChar (ZMod p) (a⁻¹ * q) = 1
      have hai : quadraticChar (ZMod p) a⁻¹ = -1 := by
        have hx : quadraticChar (ZMod p) a⁻¹ * quadraticChar (ZMod p) a = 1 := by
          rw [← map_mul]
          simp [ha0]
        rw [ha] at hx
        omega
      rw [map_mul, hai, hq]
      norm_num
    · intro q hq
      simp [ha0]
    · intro q hq
      simp [ha0]
  have hdis : Disjoint R N := by
    rw [Finset.disjoint_left]
    intro q hR hN
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hR
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hN
    omega
  have hunion : R ∪ N = Finset.univ.erase 0 := by
    ext q
    simp only [Finset.mem_union, R, N, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    constructor
    · intro h
      constructor
      · intro hq
        rcases h with h | h <;> rw [hq, quadraticChar_zero] at h <;> norm_num at h
      · trivial
    · rintro ⟨hq, -⟩
      exact quadraticChar_dichotomy hq
  have hsum : R.card + N.card = p - 1 := by
    rw [← Finset.card_union_of_disjoint hdis, hunion, Finset.card_erase_of_mem]
    · simp [ZMod.card]
    · simp
  have hRcard : R.card = (p - 1) / 2 := by omega
  have hNcard : N.card = (p - 1) / 2 := by omega
  constructor
  · refine ⟨R, ?_, hRcard, ?_⟩
    · simp [R]
    · intro q hq
      have hq0 : q ≠ 0 := by
        intro h
        simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hq
        rw [h, quadraticChar_zero] at hq
        norm_num at hq
      have hs : IsSquare q := (quadraticChar_one_iff_isSquare hq0).mp (by simpa [R] using hq)
      rcases hs with ⟨x, rfl⟩
      exact ⟨x, by simp [pow_two]⟩
  · refine ⟨N, ?_, hNcard, ?_⟩
    · simp [N]
    · intro q hq
      have hn : ¬ IsSquare q := quadraticChar_neg_one_iff_not_isSquare.mp (by simpa [N] using hq)
      rintro ⟨x, rfl⟩
      exact hn ⟨x, by simp [pow_two]⟩
