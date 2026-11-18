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
theorem problem_statement :
  ∀ (S : Finset (ℤ × ℤ)),
  ∃ (coloring : (ℤ × ℤ) → Bool),
    (∀ (x : ℤ),
      let white_points := Finset.filter (fun p => p.2 = x ∧ coloring p = true) S
      let red_points := Finset.filter (fun p => p.2 = x ∧ coloring p = false) S
      |(white_points.card : ℤ) - (red_points.card : ℤ)| ≤ 1) ∧
    (∀ (y : ℤ),
      let white_points := Finset.filter (fun p => p.1 = y ∧ coloring p = true) S
      let red_points := Finset.filter (fun p => p.1 = y ∧ coloring p = false) S
      |(white_points.card : ℤ) - (red_points.card : ℤ)| ≤ 1) := by
  intro S
  have href := imo1986_p6_assumed S
  simp only [does_exist, if_true] at href
  rcases href with ⟨ε, hε, h₁, h₂⟩
  let coloring : (ℤ × ℤ) → Bool := fun p => decide (ε p = 1)
  have count_eq (coord : ℤ × ℤ → Prop) [DecidablePred coord] :
      (∑ p ∈ S.filter coord, (if coloring p then 1 else -1 : ℤ)) =
        ((S.filter (fun p => coord p ∧ coloring p = true)).card : ℤ) -
        ((S.filter (fun p => coord p ∧ coloring p = false)).card : ℤ) := by
    rw [Finset.sum_ite]
    simp [Finset.filter_filter, sub_eq_add_neg]
  have value_eq : ∀ p ∈ S, ε p = if coloring p then 1 else -1 := by
    intro p hp
    rcases hε p hp with hp1 | hpm1
    · simp [coloring, hp1]
    · simp [coloring, hpm1]
  refine ⟨coloring, ?_, ?_⟩
  · intro x
    dsimp only
    have hsum :
        (∑ p ∈ S.filter (fun p => p.2 = x), ε p) =
          ((S.filter (fun p => p.2 = x ∧ coloring p = true)).card : ℤ) -
          ((S.filter (fun p => p.2 = x ∧ coloring p = false)).card : ℤ) := by
      calc
        _ = ∑ p ∈ S.filter (fun p => p.2 = x),
              (if coloring p then 1 else -1 : ℤ) := by
              apply Finset.sum_congr rfl
              intro p hp
              exact value_eq p (Finset.mem_of_mem_filter p hp)
        _ = _ := count_eq (fun p => p.2 = x)
    rw [← hsum]
    exact h₂ x
  · intro y
    dsimp only
    have hsum :
        (∑ p ∈ S.filter (fun p => p.1 = y), ε p) =
          ((S.filter (fun p => p.1 = y ∧ coloring p = true)).card : ℤ) -
          ((S.filter (fun p => p.1 = y ∧ coloring p = false)).card : ℤ) := by
      calc
        _ = ∑ p ∈ S.filter (fun p => p.1 = y),
              (if coloring p then 1 else -1 : ℤ) := by
              apply Finset.sum_congr rfl
              intro p hp
              exact value_eq p (Finset.mem_of_mem_filter p hp)
        _ = _ := count_eq (fun p => p.1 = y)
    rw [← hsum]
    exact h₁ y
