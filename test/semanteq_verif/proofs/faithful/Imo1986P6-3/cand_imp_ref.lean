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
theorem problem_statement_assumed (s : Finset (ℤ × ℤ)) :
  ∃ (color : (ℤ × ℤ) → Bool),
    (∀ y : ℤ, balancedOnLine color (pointsOnHorizontalLine s y)) ∧
    (∀ x : ℤ, balancedOnLine color (pointsOnVerticalLine s x)) :=
by
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
  classical
  obtain ⟨color, hy, hx⟩ := problem_statement_assumed S
  let ε : ℤ × ℤ → ℤ := fun p => if color p = true then 1 else -1
  have hsum (t : Finset (ℤ × ℤ)) :
      (∑ p ∈ t, ε p) =
        Int.ofNat (countWhite t color) - Int.ofNat (countRed t color) := by
    induction t using Finset.induction_on with
    | empty => simp [countWhite, countRed]
    | @insert a t hat ih =>
        cases ha : color a <;>
          simp [countWhite, countRed, ε, Finset.filter_insert, hat, ih, ha] <;> omega
  simp only [does_exist, Bool.true_eq, if_true]
  refine ⟨ε, ?_, ?_, ?_⟩
  · intro p hp
    cases ha : color p <;> simp [ε, ha]
  · intro x
    rw [hsum (S.filter (fun p => p.1 = x))]
    simpa [balancedOnLine, pointsOnVerticalLine] using hx x
  · intro y
    rw [hsum (S.filter (fun p => p.2 = y))]
    simpa [balancedOnLine, pointsOnHorizontalLine] using hy y
