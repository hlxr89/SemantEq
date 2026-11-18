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
  obtain ⟨ε, hε, hvertical, hhorizontal⟩ := by
    simpa [does_exist] using imo1986_p6_assumed S
  let color : ℤ × ℤ → Bool := fun p => decide (ε p = 1)
  have hsum (T : Finset (ℤ × ℤ)) (hTS : T ⊆ S) :
      ((T.filter (fun p => color p = true)).card : ℤ) -
          ((T.filter (fun p => color p = false)).card : ℤ) =
        ∑ p ∈ T, ε p := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert p T hp ih =>
        have hpS : p ∈ S := hTS (Finset.mem_insert_self p T)
        have hTS' : T ⊆ S := fun q hq => hTS (Finset.mem_insert_of_mem hq)
        rcases p with ⟨a, b⟩
        rcases hε a b hpS with hpε | hpε
        · have hcolor : color (a, b) = true := by simp [color, hpε]
          rw [Finset.filter_insert, Finset.filter_insert]
          rw [if_pos hcolor, if_neg (by simp [hcolor])]
          simp [hp, hpε, ← ih hTS'] <;> omega
        · have hcolor : color (a, b) = false := by simp [color, hpε]
          rw [Finset.filter_insert, Finset.filter_insert]
          rw [if_neg (by simp [hcolor]), if_pos hcolor]
          simp [hp, hpε, ← ih hTS'] <;> omega
  refine ⟨color, ?_, ?_⟩
  · intro x
    dsimp
    rw [hsum (S.filter (fun p => p.1 = x)) (Finset.filter_subset _ _)]
    have h : ((∑ p ∈ S.filter (fun p => p.1 = x), ε p).natAbs : ℤ) ≤ 1 := by
      simpa only [Int.natCast_natAbs] using hvertical x
    exact_mod_cast h
  · intro y
    dsimp
    rw [hsum (S.filter (fun p => p.2 = y)) (Finset.filter_subset _ _)]
    have h : ((∑ p ∈ S.filter (fun p => p.2 = y), ε p).natAbs : ℤ) ≤ 1 := by
      simpa only [Int.natCast_natAbs] using hhorizontal y
    exact_mod_cast h
