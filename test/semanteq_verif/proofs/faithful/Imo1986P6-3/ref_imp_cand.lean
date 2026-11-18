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
  obtain ⟨ε, hε, hx, hy⟩ := by
    simpa [does_exist] using imo1986_p6_assumed s
  let color : (ℤ × ℤ) → Bool := fun p => decide (ε p = 1)
  have hsum (t : Finset (ℤ × ℤ)) (ht : ∀ p ∈ t, ε p = 1 ∨ ε p = -1) :
      (∑ p ∈ t, ε p) =
        Int.ofNat (countWhite t color) - Int.ofNat (countRed t color) := by
    induction t using Finset.induction_on with
    | empty => simp [countWhite, countRed]
    | @insert a t hat ih =>
        have hta : ε a = 1 ∨ ε a = -1 := ht a (by simp)
        have htt : ∀ p ∈ t, ε p = 1 ∨ ε p = -1 := by
          intro p hp
          exact ht p (by simp [hp])
        rcases hta with ha | ha
        · simp [countWhite, countRed, color, Finset.filter_insert, hat, ih htt, ha] <;> omega
        · simp [countWhite, countRed, color, Finset.filter_insert, hat, ih htt, ha] <;> omega
  refine ⟨color, ?_, ?_⟩
  · intro y
    rw [balancedOnLine, ← hsum (pointsOnHorizontalLine s y)]
    · exact hy y
    · intro p hp
      have hp' : p ∈ s ∧ p.2 = y := by
        simpa [pointsOnHorizontalLine] using hp
      exact hε p.1 p.2 hp'.1
  · intro x
    rw [balancedOnLine, ← hsum (pointsOnVerticalLine s x)]
    · exact hx x
    · intro p hp
      have hp' : p ∈ s ∧ p.1 = x := by
        simpa [pointsOnVerticalLine] using hp
      exact hε p.1 p.2 hp'.1
