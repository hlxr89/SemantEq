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
  obtain ⟨color, hvertical, hhorizontal⟩ := problem_statement_assumed S
  simp only [does_exist, ↓reduceIte]
  let ε : ℤ × ℤ → ℤ := fun p => if color p = true then 1 else -1
  have hsum (T : Finset (ℤ × ℤ)) :
      ∑ p ∈ T, ε p =
        ((T.filter (fun p => color p = true)).card : ℤ) -
          ((T.filter (fun p => color p = false)).card : ℤ) := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert p T hp ih =>
        rw [Finset.filter_insert, Finset.filter_insert]
        cases hcolor : color p <;> simp [ε, hp, hcolor, ih] <;> omega
  refine ⟨ε, ?_, ?_, ?_⟩
  · intro p hp
    cases hcolor : color p <;> simp [ε, hcolor]
  · intro x
    rw [hsum]
    have h := hvertical x
    dsimp at h
    have h' :
        (((((S.filter (fun p => p.1 = x)).filter (fun p => color p = true)).card : ℤ) -
          (((S.filter (fun p => p.1 = x)).filter (fun p => color p = false)).card : ℤ)).natAbs : ℤ) ≤ 1 := by
      exact_mod_cast h
    simpa only [Int.natCast_natAbs] using h'
  · intro y
    rw [hsum]
    have h := hhorizontal y
    dsimp at h
    have h' :
        (((((S.filter (fun p => p.2 = y)).filter (fun p => color p = true)).card : ℤ) -
          (((S.filter (fun p => p.2 = y)).filter (fun p => color p = false)).card : ℤ)).natAbs : ℤ) ≤ 1 := by
      exact_mod_cast h
    simpa only [Int.natCast_natAbs] using h'
