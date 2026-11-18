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
  simp only [does_exist]
  obtain ⟨coloring, hcoloring, hx, hy⟩ := problem_statement_assumed S
  let ε : ℤ × ℤ → ℤ := fun p => if coloring p = false then 1 else -1
  have count_identity (T : Finset (ℤ × ℤ)) :
      ((T.filter (fun p => coloring p = false)).card : ℤ) -
          ((T.filter (fun p => coloring p = true)).card : ℤ) =
        ∑ p ∈ T, ε p := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert a T ha ih =>
        simp only [ε] at ih
        rw [Finset.filter_insert, Finset.filter_insert, Finset.sum_insert ha]
        cases hca : coloring a <;> simp [ha, hca, ih, ε] <;> omega
  refine ⟨ε, ?_, ?_, ?_⟩
  · intro p hp
    cases hcp : coloring p <;> simp [ε, hcp]
  · intro x
    have hid := count_identity (S.filter (fun p => p.1 = x))
    rw [← hid, Int.abs_eq_natAbs]
    exact_mod_cast hx x
  · intro y
    have hid := count_identity (S.filter (fun p => p.2 = y))
    rw [← hid, Int.abs_eq_natAbs]
    exact_mod_cast hy y
