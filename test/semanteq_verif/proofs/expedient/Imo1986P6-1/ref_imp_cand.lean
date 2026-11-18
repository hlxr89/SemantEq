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
  classical
  obtain ⟨ε, hε, hx, hy⟩ := imo1986_p6_assumed S
  have count_eq (T : Finset (ℤ × ℤ)) (hT : ∀ p ∈ T, ε p = 1 ∨ ε p = -1) :
      ∑ p ∈ T, ε p = ((T.filter (fun p => ¬ ε p = -1)).card : ℤ) -
        ((T.filter (fun p => ε p = -1)).card : ℤ) := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert a T ha ih =>
      simp only [Finset.mem_insert] at hT
      have hea := hT a (Or.inl rfl)
      have heT : ∀ p ∈ T, ε p = 1 ∨ ε p = -1 := fun p hp => hT p (Or.inr hp)
      simp only [Finset.filter_insert]
      rcases hea with hea | hea <;> simp [ha, ih heT, hea] <;> ring
  refine ⟨fun p => decide (ε p = -1), ?_, ?_, ?_⟩
  · intro p hp
    by_cases h : ε p = -1 <;> simp [h]
  · intro x
    dsimp
    have he := count_eq (S.filter (fun p => p.1 = x)) (by
      intro p hp
      exact hε p (Finset.mem_filter.mp hp).1)
    have hb := hx x
    simp only [decide_eq_true_eq, decide_eq_false_iff_not]
    rw [he] at hb
    rw [Int.abs_eq_natAbs] at hb
    exact_mod_cast hb
  · intro y
    dsimp
    have he := count_eq (S.filter (fun p => p.2 = y)) (by
      intro p hp
      exact hε p (Finset.mem_filter.mp hp).1)
    have hb := hy y
    simp only [decide_eq_true_eq, decide_eq_false_iff_not]
    rw [he] at hb
    rw [Int.abs_eq_natAbs] at hb
    exact_mod_cast hb
