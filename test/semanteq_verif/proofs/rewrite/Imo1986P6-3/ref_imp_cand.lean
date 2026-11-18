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
  obtain ⟨ε, hε, hx, hy⟩ := (show
    ∃ ε : ℤ × ℤ → ℤ,
      (∀ p ∈ s, ε p = 1 ∨ ε p = -1) ∧
      (∀ x : ℤ, |∑ p ∈ s.filter (fun p => p.1 = x), ε p| ≤ 1) ∧
      (∀ y : ℤ, |∑ p ∈ s.filter (fun p => p.2 = y), ε p| ≤ 1)
    from by simpa only [does_exist, if_true] using imo1986_p6_assumed s)
  let color : (ℤ × ℤ) → Bool := fun p => decide (ε p = 1)
  have hsum (pts : Finset (ℤ × ℤ)) (hpts : pts ⊆ s) :
      Int.ofNat (countWhite pts color) - Int.ofNat (countRed pts color) =
        ∑ p ∈ pts, ε p := by
    rw [show countWhite pts color = (pts.filter fun p => ε p = 1).card by
      simp only [countWhite, color, decide_eq_true_eq]]
    rw [show countRed pts color = (pts.filter fun p => ε p ≠ 1).card by
      simp only [countRed, color, decide_eq_false_iff_not]]
    rw [show (∑ p ∈ pts, ε p) = ∑ p ∈ pts, if ε p = 1 then 1 else -1 from
      Finset.sum_congr rfl (fun p hp => by
        rcases hε p (hpts hp) with hp1 | hpneg
        · rw [hp1, if_pos rfl]
        · rw [hpneg, if_neg]
          intro h
          cases h)]
    simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one, mul_neg,
      Int.ofNat_eq_natCast, sub_eq_add_neg]
  refine ⟨color, ?_, ?_⟩
  · intro y
    rw [balancedOnLine, hsum (pointsOnHorizontalLine s y) (Finset.filter_subset _ _)]
    exact hy y
  · intro x
    rw [balancedOnLine, hsum (pointsOnVerticalLine s x) (Finset.filter_subset _ _)]
    exact hx x
