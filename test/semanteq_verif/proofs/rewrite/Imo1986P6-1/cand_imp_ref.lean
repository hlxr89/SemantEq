import Mathlib
open Finset

-- ===== unified context (both sides' local defs, merged) =====
abbrev does_exist : Bool := true

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (S : Finset (ℤ × ℤ)) :
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
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1986_p6 (S : Finset (ℤ × ℤ)) :
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
  simp only [does_exist, if_true]
  obtain ⟨coloring, hcoloring, hx, hy⟩ := problem_statement_assumed S
  let ε : ℤ × ℤ → ℤ := fun p => if coloring p = true then -1 else 1
  have count_sum (T : Finset (ℤ × ℤ)) :
      (∑ p ∈ T, ε p) =
        ((T.filter (fun p => coloring p = false)).card : ℤ) -
        ((T.filter (fun p => coloring p = true)).card : ℤ) := by
    change (∑ p ∈ T, (if coloring p = true then -1 else 1 : ℤ)) = _
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_neg, mul_one]
    rw [show (T.filter fun p => coloring p ≠ true) =
        T.filter (fun p => coloring p = false) by
      apply Finset.filter_congr
      intro p hp
      cases coloring p <;> simp only [ne_eq, Bool.false_eq_true,
        not_false_eq_true, not_true_eq_false, Bool.true_eq_false]]
    rw [neg_add_eq_sub]
  refine ⟨ε, ?_, ?_, ?_⟩
  · intro p hp
    rcases hcoloring p hp with ht | hf
    · right
      simp only [ε, ht, ↓reduceIte]
    · left
      simp only [ε, hf, Bool.false_eq_true, ↓reduceIte]
  · intro x
    have h := hx x
    dsimp only at h
    rw [count_sum]
    rw [← Int.natCast_natAbs]
    exact Int.ofNat_le.mpr h
  · intro y
    have h := hy y
    dsimp only at h
    rw [count_sum]
    rw [← Int.natCast_natAbs]
    exact Int.ofNat_le.mpr h
