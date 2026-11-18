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
  obtain ⟨ε, hε, hx, hy⟩ := by
    simpa [does_exist] using imo1986_p6_assumed S
  let coloring : ℤ × ℤ → Bool := fun p => if ε p = -1 then true else false
  refine ⟨coloring, ?_, ?_, ?_⟩
  · intro p hp
    cases coloring p <;> simp
  · intro x
    dsimp only
    have hsum :
        (∑ p ∈ S.filter (fun p => p.1 = x), ε p) =
          ((S.filter (fun p => p.1 = x)).filter (fun p => coloring p = false)).card -
          ((S.filter (fun p => p.1 = x)).filter (fun p => coloring p = true)).card := by
      calc
        (∑ p ∈ S.filter (fun p => p.1 = x), ε p) =
            ∑ p ∈ S.filter (fun p => p.1 = x),
              (if coloring p = false then (1 : ℤ) else -1) := by
                apply Finset.sum_congr rfl
                intro p hp
                have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
                rcases hε p.1 p.2 hpS with h | h <;> simp [coloring, h]
        _ = _ := by
          rw [Finset.sum_ite]
          simp [sub_eq_add_neg]
    rw [← hsum]
    have hcast :
        (↑(Int.natAbs (∑ p ∈ S.filter (fun p => p.1 = x), ε p)) : ℤ) ≤ (1 : ℤ) := by
      simpa [Int.natCast_natAbs] using hx x
    exact_mod_cast hcast
  · intro y
    dsimp only
    have hsum :
        (∑ p ∈ S.filter (fun p => p.2 = y), ε p) =
          ((S.filter (fun p => p.2 = y)).filter (fun p => coloring p = false)).card -
          ((S.filter (fun p => p.2 = y)).filter (fun p => coloring p = true)).card := by
      calc
        (∑ p ∈ S.filter (fun p => p.2 = y), ε p) =
            ∑ p ∈ S.filter (fun p => p.2 = y),
              (if coloring p = false then (1 : ℤ) else -1) := by
                apply Finset.sum_congr rfl
                intro p hp
                have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
                rcases hε p.1 p.2 hpS with h | h <;> simp [coloring, h]
        _ = _ := by
          rw [Finset.sum_ite]
          simp [sub_eq_add_neg]
    rw [← hsum]
    have hcast :
        (↑(Int.natAbs (∑ p ∈ S.filter (fun p => p.2 = y), ε p)) : ℤ) ≤ (1 : ℤ) := by
      simpa [Int.natCast_natAbs] using hy y
    exact_mod_cast hcast
