import Mathlib
open Finset

-- ===== unified context (both sides' local defs, merged) =====
abbrev does_exist : Bool := true

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
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
  simp only [does_exist, ↓reduceIte]
  obtain ⟨coloring, h₂, h₁⟩ := problem_statement_assumed S
  let ε : ℤ × ℤ → ℤ := fun p => if coloring p = true then 1 else -1
  have hbridge (coord : ℤ × ℤ → Prop) [DecidablePred coord] :
      (∑ p ∈ S.filter coord, ε p) =
        ((S.filter (fun p => coord p ∧ coloring p = true)).card : ℤ) -
        ((S.filter (fun p => coord p ∧ coloring p = false)).card : ℤ) := by
    unfold ε
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, mul_neg]
    have htrue :
        (S.filter coord).filter (fun p => coloring p = true) =
          S.filter (fun p => coord p ∧ coloring p = true) := by
      exact Finset.filter_filter coord (fun p => coloring p = true) S
    have hfalse :
        (S.filter coord).filter (fun p => ¬ coloring p = true) =
          S.filter (fun p => coord p ∧ coloring p = false) := by
      ext p
      simp only [Finset.mem_filter, Bool.eq_false_iff]
      constructor
      · rintro ⟨⟨hp, hc⟩, hn⟩
        exact ⟨hp, hc, hn⟩
      · rintro ⟨hp, hc, hn⟩
        exact ⟨⟨hp, hc⟩, hn⟩
    rw [htrue, hfalse]
    simp only [sub_eq_add_neg]
  refine ⟨ε, ?_, ?_, ?_⟩
  · intro p hp
    unfold ε
    by_cases h : coloring p = true
    · simp only [h, ↓reduceIte, true_or]
    · have hf : coloring p = false := Bool.eq_false_iff.mpr h
      rw [hf]
      simp only [Bool.false_eq_true, ↓reduceIte, or_true]
  · intro x
    rw [hbridge]
    exact h₁ x
  · intro y
    rw [hbridge]
    exact h₂ y
