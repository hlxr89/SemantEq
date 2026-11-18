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
  obtain ⟨ε, hε, hv, hh⟩ := by
    simpa only [does_exist, if_true] using imo1986_p6_assumed S
  refine ⟨fun p => decide (ε p = 1), ?_, ?_⟩
  · intro x
    have hsum :
        (∑ p ∈ S.filter (fun p => p.1 = x), ε p) =
          ((S.filter (fun p => p.1 = x)).filter
              (fun p => decide (ε p = 1) = true)).card -
          ((S.filter (fun p => p.1 = x)).filter
              (fun p => decide (ε p = 1) = false)).card := by
      have hpoint : ∀ p ∈ S.filter (fun p => p.1 = x),
          ε p = if decide (ε p = 1) = true then 1 else -1 := by
        intro p hp
        rcases hε p (Finset.mem_filter.mp hp).1 with hp | hp
        · simp only [hp, decide_true, if_true]
        · rw [hp]
          have hn : (-1 : ℤ) ≠ 1 := by
            intro h
            exact Int.noConfusion h
          rw [(Bool.decide_false_iff ((-1 : ℤ) = 1)).2 hn]
          rw [if_neg Bool.false_ne_true]
      rw [Finset.sum_congr rfl hpoint]
      simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one,
        mul_neg_one, sub_eq_add_neg, Bool.eq_false_eq_not_eq_true]
    apply Int.ofNat_le.mp
    rw [Int.natCast_natAbs, ← hsum]
    exact hv x
  · intro y
    have hsum :
        (∑ p ∈ S.filter (fun p => p.2 = y), ε p) =
          ((S.filter (fun p => p.2 = y)).filter
              (fun p => decide (ε p = 1) = true)).card -
          ((S.filter (fun p => p.2 = y)).filter
              (fun p => decide (ε p = 1) = false)).card := by
      have hpoint : ∀ p ∈ S.filter (fun p => p.2 = y),
          ε p = if decide (ε p = 1) = true then 1 else -1 := by
        intro p hp
        rcases hε p (Finset.mem_filter.mp hp).1 with hp | hp
        · simp only [hp, decide_true, if_true]
        · rw [hp]
          have hn : (-1 : ℤ) ≠ 1 := by
            intro h
            exact Int.noConfusion h
          rw [(Bool.decide_false_iff ((-1 : ℤ) = 1)).2 hn]
          rw [if_neg Bool.false_ne_true]
      rw [Finset.sum_congr rfl hpoint]
      simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one,
        mul_neg_one, sub_eq_add_neg, Bool.eq_false_eq_not_eq_true]
    apply Int.ofNat_le.mp
    rw [Int.natCast_natAbs, ← hsum]
    exact hh y
