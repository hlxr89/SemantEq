import Mathlib
open Finset

-- ===== unified context (both sides' local defs, merged) =====
abbrev does_exist : Bool := true

-- ===== assumed statement (antecedent) =====
theorem imo1986_p6_assumed (S : Finset (ℤ × ℤ)) :
    if does_exist then
      ∃ ε : ℤ × ℤ → ℤ,
        (∀ p ∈ S, ε p = 1 ∨ ε p = -1) ∧
        (∀ x : ℤ, |∑ p ∈ S.filter (fun p => p.1 = x), ε p| ≤ 1) ∧
        (∀ y : ℤ, |∑ p ∈ S.filter (fun p => p.2 = y), ε p| ≤ 1)
    else
      ¬ ∃ ε : ℤ × ℤ → ℤ,
        (∀ p ∈ S, ε p = 1 ∨ ε p = -1) ∧
        (∀ x : ℤ, |∑ p ∈ S.filter (fun p => p.1 = x), ε p| ≤ 1) ∧
        (∀ y : ℤ, |∑ p ∈ S.filter (fun p => p.2 = y), ε p| ≤ 1) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (S : Finset (ℤ × ℤ)) :
  ∃ (coloring : ℤ × ℤ → Bool),
    (∀ p ∈ S, coloring p = true ∨ coloring p = false) ∧
    (∀ x : ℤ, 
      let points_on_line := S.filter (fun p => p.1 = x)
      let red_count := (points_on_line.filter (fun p => coloring p = true)).card
      let white_count := (points_on_line.filter (fun p => coloring p = false)).card
      Int.natAbs (white_count - red_count) ≤ 1) ∧
    (∀ y : ℤ,
      let points_on_line := S.filter (fun p => p.2 = y)
      let red_count := (points_on_line.filter (fun p => coloring p = true)).card
      let white_count := (points_on_line.filter (fun p => coloring p = false)).card
      Int.natAbs (white_count - red_count) ≤ 1) := by
  have href := imo1986_p6_assumed S
  simp only [does_exist, if_true] at href
  obtain ⟨ε, hε, hx, hy⟩ := href
  let coloring : ℤ × ℤ → Bool := fun p => decide (ε p = -1)
  have count_sum (T : Finset (ℤ × ℤ)) (hT : ∀ p ∈ T, p ∈ S) :
      (∑ p ∈ T, ε p) =
        ((T.filter (fun p => coloring p = false)).card : ℤ) -
        ((T.filter (fun p => coloring p = true)).card : ℤ) := by
    rw [show (∑ p ∈ T, ε p) =
        ∑ p ∈ T, (if ε p = -1 then -1 else 1 : ℤ) by
      apply Finset.sum_congr rfl
      intro p hp
      rcases hε p (hT p hp) with hp1 | hpn
      · simp only [hp1, Int.reduceNeg, reduceCtorEq, ↓reduceIte]
      · simp only [hpn, ↓reduceIte]]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_neg, mul_one]
    simp only [coloring, decide_eq_false_iff_not, decide_eq_true_eq]
    rw [neg_add_eq_sub]
  refine ⟨coloring, ?_, ?_, ?_⟩
  · intro p hp
    have hpε := hε p hp
    rcases hpε with hp1 | hpn
    · right
      simp only [coloring, hp1, Int.reduceNeg, reduceCtorEq, decide_false]
    · left
      simp only [coloring, hpn, decide_true]
  · intro x
    dsimp only
    rw [← Int.ofNat_le]
    rw [Int.natCast_natAbs]
    rw [← count_sum (S.filter (fun p => p.1 = x)) (by
      intro p hp
      exact (Finset.mem_filter.mp hp).1)]
    exact hx x
  · intro y
    dsimp only
    rw [← Int.ofNat_le]
    rw [Int.natCast_natAbs]
    rw [← count_sum (S.filter (fun p => p.2 = y)) (by
      intro p hp
      exact (Finset.mem_filter.mp hp).1)]
    exact hy y
