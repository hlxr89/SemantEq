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
  classical
  have href := imo1986_p6_assumed S
  simp only [does_exist, if_true] at href
  rcases href with ⟨ε, hε, hv, hh⟩
  let color : ℤ × ℤ → Bool := fun p => if ε p = 1 then true else false
  have hsum (T : Finset (ℤ × ℤ)) (hTS : T ⊆ S) :
      ∑ p ∈ T, ε p =
        ((T.filter (fun p => color p = true)).card : ℤ) -
          ((T.filter (fun p => color p = false)).card : ℤ) := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert a T ha ih =>
      have haS : a ∈ S := hTS (Finset.mem_insert_self a T)
      have hT : T ⊆ S := fun p hp => hTS (Finset.mem_insert_of_mem hp)
      rw [sum_insert ha, ih hT]
      rw [Finset.filter_insert, Finset.filter_insert]
      rcases hε a haS with hp | hp <;> simp [color, hp, ha] <;> ring
  refine ⟨color, ?_, ?_⟩
  · intro x
    dsimp only
    have hs := hsum (S.filter (fun p => p.1 = x)) (Finset.filter_subset _ _)
    have h := hv x
    rw [hs] at h
    have hz :
        ((Int.natAbs
          ((((S.filter (fun p => p.1 = x)).filter (fun p => color p = true)).card : ℤ) -
            (((S.filter (fun p => p.1 = x)).filter (fun p => color p = false)).card : ℤ))) : ℤ) ≤ 1 := by
      simpa only [Int.natCast_natAbs] using h
    omega
  · intro y
    dsimp only
    have hs := hsum (S.filter (fun p => p.2 = y)) (Finset.filter_subset _ _)
    have h := hh y
    rw [hs] at h
    have hz :
        ((Int.natAbs
          ((((S.filter (fun p => p.2 = y)).filter (fun p => color p = true)).card : ℤ) -
            (((S.filter (fun p => p.2 = y)).filter (fun p => color p = false)).card : ℤ))) : ℤ) ≤ 1 := by
      simpa only [Int.natCast_natAbs] using h
    omega
