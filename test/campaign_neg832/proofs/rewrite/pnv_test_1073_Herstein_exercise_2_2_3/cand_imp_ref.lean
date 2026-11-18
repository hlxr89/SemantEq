import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (G : Type*) [Group G] (h : ∀ (a b : G) (i : ℕ), (a * b)^i = a^i * b^i → (a * b)^(i+1) = a^(i+1) * b^(i+1)) : ∀ a b : G, a * b = b * a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_2_3 {G : Type*} [Group G]
  {P : ℕ → Prop} {hP : P = λ i => ∀ a b : G, (a*b)^i = a^i * b^i}
  (hP1 : ∃ n : ℕ, P n ∧ P (n+1) ∧ P (n+2)) : 
  ∀ a b : G, a*b = b*a := by
  subst P
  obtain ⟨n, hn, hn1, hn2⟩ := hP1
  apply dummy_assumed G
  intro a b i hi
  have hab : a * b = b * a := by
    have e1 : b ^ n * a = a * b ^ n := by
      apply mul_left_cancel (a := a ^ n)
      apply mul_right_cancel (b := b)
      have step : (a ^ n * b ^ n) * (a * b) =
          a ^ (n + 1) * b ^ (n + 1) :=
        (congrArg (fun x => x * (a * b)) (hn a b)).symm.trans
          (by simpa only [pow_succ] using hn1 a b)
      simpa only [pow_succ, mul_assoc] using step
    have e2 : b ^ (n + 1) * a = a * b ^ (n + 1) := by
      apply mul_left_cancel (a := a ^ (n + 1))
      apply mul_right_cancel (b := b)
      have step : (a ^ (n + 1) * b ^ (n + 1)) * (a * b) =
          a ^ (n + 2) * b ^ (n + 2) :=
        (congrArg (fun x => x * (a * b)) (hn1 a b)).symm.trans
          (by simpa only [pow_succ] using hn2 a b)
      simpa only [pow_succ, mul_assoc] using step
    have e2' : (b ^ n * b) * a = a * (b ^ n * b) := by
      simpa only [pow_succ] using e2
    have e2'' : b ^ n * (b * a) = (a * b ^ n) * b := by
      simpa only [mul_assoc] using e2'
    rw [← e1] at e2''
    apply Eq.symm
    apply mul_left_cancel (a := b ^ n)
    simpa only [mul_assoc] using e2''
  exact (show Commute a b from hab).mul_pow (i + 1)
