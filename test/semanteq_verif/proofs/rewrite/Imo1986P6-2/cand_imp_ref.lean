import Mathlib

open Finset

-- ===== unified context (both sides' local defs, merged) =====
abbrev does_exist : Bool := true

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (S : Finset (ℤ × ℤ)) :
  ∃ (color : ℤ × ℤ → Bool), 
    (∀ (x : ℤ), 
      let points_on_vertical_line := S.filter (fun p => p.1 = x)
      let white_points := points_on_vertical_line.filter (fun p => color p = true)
      let red_points := points_on_vertical_line.filter (fun p => color p = false)
      Int.natAbs ((white_points.card : ℤ) - (red_points.card : ℤ)) ≤ 1) ∧
    (∀ (y : ℤ),
      let points_on_horizontal_line := S.filter (fun p => p.2 = y)
      let white_points := points_on_horizontal_line.filter (fun p => color p = true)
      let red_points := points_on_horizontal_line.filter (fun p => color p = false)
      Int.natAbs ((white_points.card : ℤ) - (red_points.card : ℤ)) ≤ 1) := by
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
  obtain ⟨color, hv, hh⟩ := problem_statement_assumed S
  refine ⟨fun p => if color p = true then 1 else -1, ?_, ?_, ?_⟩
  · intro p hp
    by_cases h : color p = true
    · exact Or.inl (if_pos h)
    · exact Or.inr (if_neg h)
  · intro x
    have hsum :
        (∑ p ∈ S.filter (fun p => p.1 = x),
          if color p = true then (1 : ℤ) else -1) =
          ((S.filter (fun p => p.1 = x)).filter
              (fun p => color p = true)).card -
          ((S.filter (fun p => p.1 = x)).filter
              (fun p => color p = false)).card := by
      simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one,
        mul_neg_one, sub_eq_add_neg, Bool.eq_false_eq_not_eq_true]
    rw [hsum, Int.abs_eq_natAbs]
    exact Int.ofNat_le.mpr (hv x)
  · intro y
    have hsum :
        (∑ p ∈ S.filter (fun p => p.2 = y),
          if color p = true then (1 : ℤ) else -1) =
          ((S.filter (fun p => p.2 = y)).filter
              (fun p => color p = true)).card -
          ((S.filter (fun p => p.2 = y)).filter
              (fun p => color p = false)).card := by
      simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one,
        mul_neg_one, sub_eq_add_neg, Bool.eq_false_eq_not_eq_true]
    rw [hsum, Int.abs_eq_natAbs]
    exact Int.ofNat_le.mpr (hh y)
