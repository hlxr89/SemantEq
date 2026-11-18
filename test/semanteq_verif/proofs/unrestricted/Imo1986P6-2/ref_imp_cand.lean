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
  have href := imo1986_p6_assumed S
  simp only [does_exist, Bool.if_true_right] at href
  obtain ⟨ε, hε, hx, hy⟩ := href
  let color : ℤ × ℤ → Bool := fun p => if ε p = 1 then true else false
  have balance (T : Finset (ℤ × ℤ)) (hT : ∀ p ∈ T, p ∈ S) :
      ∑ p ∈ T, ε p =
        ((T.filter (fun p => color p = true)).card : ℤ) -
        ((T.filter (fun p => color p = false)).card : ℤ) := by
    classical
    induction T using Finset.induction_on with
    | empty => simp
    | @insert a T ha ih =>
      have haS : a ∈ S := hT a (by simp)
      have hTS : ∀ p ∈ T, p ∈ S := by
        intro p hp
        exact hT p (by simp [hp])
      rcases hε a haS with hpos | hneg
      · rw [Finset.sum_insert ha, ih hTS]
        simp only [Finset.filter_insert]
        simp [color, hpos, ha]
        omega
      · have hnot : ε a ≠ 1 := by omega
        rw [Finset.sum_insert ha, ih hTS]
        simp only [Finset.filter_insert]
        simp [color, hnot, hneg, ha]
        omega
  refine ⟨color, ?_, ?_⟩
  · intro x
    have hsub : ∀ p ∈ S.filter (fun p => p.1 = x), p ∈ S := by
      intro p hp
      exact (Finset.mem_filter.mp hp).1
    have hb := balance (S.filter (fun p => p.1 = x)) hsub
    have h := hx x
    rw [hb] at h
    dsimp
    have hi :
        (((((S.filter (fun p => p.1 = x)).filter (fun p => color p = true)).card : ℤ) -
          (((S.filter (fun p => p.1 = x)).filter (fun p => color p = false)).card : ℤ)).natAbs : ℤ) ≤ 1 := by
      simpa only [Int.natCast_natAbs] using h
    exact_mod_cast hi
  · intro y
    have hsub : ∀ p ∈ S.filter (fun p => p.2 = y), p ∈ S := by
      intro p hp
      exact (Finset.mem_filter.mp hp).1
    have hb := balance (S.filter (fun p => p.2 = y)) hsub
    have h := hy y
    rw [hb] at h
    dsimp
    have hi :
        (((((S.filter (fun p => p.2 = y)).filter (fun p => color p = true)).card : ℤ) -
          (((S.filter (fun p => p.2 = y)).filter (fun p => color p = false)).card : ℤ)).natAbs : ℤ) ≤ 1 := by
      simpa only [Int.natCast_natAbs] using h
    exact_mod_cast hi
