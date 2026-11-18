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
  simp only [does_exist, ↓reduceIte] at href
  obtain ⟨ε, hε, h₁, h₂⟩ := href
  let coloring : ℤ × ℤ → Bool := fun p => decide (ε p = 1)
  have hbridge (coord : ℤ × ℤ → Prop) [DecidablePred coord] :
      (∑ p ∈ S.filter coord, ε p) =
        ((S.filter (fun p => coord p ∧ coloring p = true)).card : ℤ) -
        ((S.filter (fun p => coord p ∧ coloring p = false)).card : ℤ) := by
    have hpoint (p : ℤ × ℤ) (hp : p ∈ S) :
        ε p = if coloring p = true then 1 else -1 := by
      rcases hε p hp with hp | hp
      · simp only [coloring, hp, decide_true, ↓reduceIte]
      · have hne : (-1 : ℤ) ≠ 1 := by
          intro h
          cases h
        simp only [coloring, hp, hne, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hsum :
        (S.filter coord).sum ε =
          (S.filter coord).sum (fun p => if coloring p = true then 1 else -1) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact hpoint p (Finset.mem_filter.mp hp).1
    rw [hsum]
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
  refine ⟨coloring, ?_, ?_⟩
  · intro x
    dsimp only
    rw [← hbridge]
    exact h₂ x
  · intro y
    dsimp only
    rw [← hbridge]
    exact h₁ y
