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
  classical
  have h := imo1986_p6_assumed S
  simp only [does_exist, if_true] at h
  obtain ⟨ε, hε, hx, hy⟩ := h
  let coloring : (ℤ × ℤ) → Bool := fun p => decide (ε p = 1)
  have count_eq (T : Finset (ℤ × ℤ)) (hT : ∀ p ∈ T, ε p = 1 ∨ ε p = -1) :
      ∑ p ∈ T, ε p =
        ((T.filter fun p => coloring p = true).card : ℤ) -
          ((T.filter fun p => coloring p = false).card : ℤ) := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert p T hp ih =>
        have hpε := hT p (Finset.mem_insert_self p T)
        have hTε : ∀ q ∈ T, ε q = 1 ∨ ε q = -1 := by
          intro q hq
          exact hT q (Finset.mem_insert_of_mem hq)
        rw [Finset.sum_insert hp, ih hTε]
        rw [Finset.filter_insert, Finset.filter_insert]
        rcases hpε with hpε | hpε
        · simp [coloring, hpε, hp] <;> ring
        · simp [coloring, hpε, hp] <;> ring
  refine ⟨coloring, ?_, ?_⟩
  · intro x
    dsimp only
    have hline := hy x
    rw [count_eq (S.filter fun p => p.2 = x) (by
      intro p hp
      exact hε p (Finset.mem_filter.mp hp).1)] at hline
    simpa only [Finset.filter_filter] using hline
  · intro y
    dsimp only
    have hline := hx y
    rw [count_eq (S.filter fun p => p.1 = y) (by
      intro p hp
      exact hε p (Finset.mem_filter.mp hp).1)] at hline
    simpa only [Finset.filter_filter] using hline
