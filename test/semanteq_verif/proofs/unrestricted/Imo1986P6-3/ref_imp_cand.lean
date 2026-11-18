import Mathlib

open Finset

-- ===== unified context (both sides' local defs, merged) =====
abbrev does_exist : Bool := true

def pointsOnHorizontalLine (s : Finset (ℤ × ℤ)) (y : ℤ) : Finset (ℤ × ℤ) :=
  s.filter (fun p => p.2 = y)

def pointsOnVerticalLine (s : Finset (ℤ × ℤ)) (x : ℤ) : Finset (ℤ × ℤ) :=
  s.filter (fun p => p.1 = x)

def countWhite (pts : Finset (ℤ × ℤ)) (color : (ℤ × ℤ) → Bool) : ℕ :=
  pts.filter (fun p => color p = true) |>.card

def countRed (pts : Finset (ℤ × ℤ)) (color : (ℤ × ℤ) → Bool) : ℕ :=
  pts.filter (fun p => color p = false) |>.card

def balancedOnLine (color : (ℤ × ℤ) → Bool) (pts : Finset (ℤ × ℤ)) : Prop :=
  |Int.ofNat (countWhite pts color) - Int.ofNat (countRed pts color)| ≤ 1

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
theorem problem_statement (s : Finset (ℤ × ℤ)) :
  ∃ (color : (ℤ × ℤ) → Bool),
    (∀ y : ℤ, balancedOnLine color (pointsOnHorizontalLine s y)) ∧
    (∀ x : ℤ, balancedOnLine color (pointsOnVerticalLine s x)) :=
by
  classical
  have href := (by simpa [does_exist] using imo1986_p6_assumed s)
  obtain ⟨ε, hε, hx, hy⟩ := href
  let color : (ℤ × ℤ) → Bool := fun p => if ε p = 1 then true else false
  have hsum (pts : Finset (ℤ × ℤ)) (hpts : pts ⊆ s) :
      (∑ p ∈ pts, ε p) =
        Int.ofNat (countWhite pts color) - Int.ofNat (countRed pts color) := by
    induction pts using Finset.induction_on with
    | empty => simp [countWhite, countRed]
    | @insert p pts hp ih =>
      have hpS : p ∈ s := hpts (Finset.mem_insert_self p pts)
      have hptsS : pts ⊆ s := fun q hq => hpts (Finset.mem_insert_of_mem hq)
      have hi := ih hptsS
      rcases hε p.1 p.2 (by simpa using hpS) with hep | hep
      · simp [countWhite, countRed, color, Finset.filter_insert, hp, hep, hi] <;> omega
      · simp [countWhite, countRed, color, Finset.filter_insert, hp, hep, hi] <;> omega
  refine ⟨color, ?_, ?_⟩
  · intro y
    unfold balancedOnLine pointsOnHorizontalLine
    rw [← hsum (s.filter fun p => p.2 = y) (Finset.filter_subset _ _)]
    exact hy y
  · intro x
    unfold balancedOnLine pointsOnVerticalLine
    rw [← hsum (s.filter fun p => p.1 = x) (Finset.filter_subset _ _)]
    exact hx x
