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
  let color : (ℤ × ℤ) → Bool := fun p => if ε p = 1 then true else false
  have hsum (pts : Finset (ℤ × ℤ)) (hpts : ∀ p ∈ pts, p ∈ s) :
      ∑ p ∈ pts, ε p =
        Int.ofNat (countWhite pts color) - Int.ofNat (countRed pts color) := by
    induction pts using Finset.induction_on with
    | empty => simp [countWhite, countRed]
    | @insert a t ha ih =>
        have hat : a ∈ s := hpts a (by simp)
        have htt : ∀ p ∈ t, p ∈ s := by
          intro p hp
          exact hpts p (by simp [hp])
        rw [sum_insert ha, ih htt]
        rcases hε a.1 a.2 (by simpa using hat) with hea | hea
        · have hea' : ε a = 1 := by simpa using hea
          simp [countWhite, countRed, Finset.filter_insert, color, ha, hea']
          ring
        · have hea' : ε a = -1 := by simpa using hea
          simp [countWhite, countRed, Finset.filter_insert, color, ha, hea']
          ring
  refine ⟨color, ?_, ?_⟩
  · intro y
    rw [balancedOnLine, ← hsum (pointsOnHorizontalLine s y) (by
      intro p hp
      exact (Finset.mem_filter.mp hp).1)]
    simpa [pointsOnHorizontalLine] using hy y
  · intro x
    rw [balancedOnLine, ← hsum (pointsOnVerticalLine s x) (by
      intro p hp
      exact (Finset.mem_filter.mp hp).1)]
    simpa [pointsOnVerticalLine] using hx x
