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
  have h := imo1986_p6_assumed S
  simp only [does_exist, Bool.if_true_right] at h
  obtain ⟨ε, hε, hx, hy⟩ := h
  have count_identity (T : Finset (ℤ × ℤ))
      (hT : ∀ p ∈ T, ε p = 1 ∨ ε p = -1) :
      ((T.filter (fun p => decide (ε p = -1) = false)).card : ℤ) -
          ((T.filter (fun p => decide (ε p = -1) = true)).card : ℤ) =
        ∑ p ∈ T, ε p := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert a T ha ih =>
        have haε := hT a (by simp)
        have hTε : ∀ p ∈ T, ε p = 1 ∨ ε p = -1 := by
          intro p hp
          exact hT p (by simp [hp])
        have ih' := ih hTε
        simp only [decide_eq_false_iff_not, decide_eq_true_eq] at ih'
        by_cases hea : ε a = -1
        · rw [Finset.filter_insert, Finset.filter_insert]
          simp [ha, hea]
          omega
        · have hea' : ε a = 1 := haε.resolve_right hea
          rw [Finset.filter_insert, Finset.filter_insert]
          simp [ha, hea, hea']
          omega
  refine ⟨fun p => decide (ε p = -1), ?_, ?_, ?_⟩
  · intro p hp
    cases hcolor : decide (ε p = -1) <;> simp [hcolor]
  · intro x
    dsimp
    have hmem : ∀ p ∈ S.filter (fun p => p.1 = x), ε p = 1 ∨ ε p = -1 := by
      intro p hp
      exact hε p (Finset.mem_filter.mp hp).1
    have hid := count_identity (S.filter (fun p => p.1 = x)) hmem
    rw [hid]
    have hb := hx x
    rw [← Int.natCast_natAbs] at hb
    exact_mod_cast hb
  · intro y
    dsimp
    have hmem : ∀ p ∈ S.filter (fun p => p.2 = y), ε p = 1 ∨ ε p = -1 := by
      intro p hp
      exact hε p (Finset.mem_filter.mp hp).1
    have hid := count_identity (S.filter (fun p => p.2 = y)) hmem
    rw [hid]
    have hb := hy y
    rw [← Int.natCast_natAbs] at hb
    exact_mod_cast hb
