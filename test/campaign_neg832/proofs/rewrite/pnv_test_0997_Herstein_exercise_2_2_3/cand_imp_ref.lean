import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] (a b : G) (h : ∀ i : ℕ, (a * b) ^ i = a^i * b^i) (i : ℕ) : a * b = b * a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_2_3 {G : Type*} [Group G]
  {P : ℕ → Prop} {hP : P = λ i => ∀ a b : G, (a*b)^i = a^i * b^i}
  (hP1 : ∃ n : ℕ, P n ∧ P (n+1) ∧ P (n+2)) : 
  ∀ a b : G, a*b = b*a := by
  subst P
  obtain ⟨n, hn, hn1, hn2⟩ := hP1
  intro a b
  have central (k : ℕ)
      (hk : ∀ x y : G, (x * y) ^ k = x ^ k * y ^ k)
      (hk1 : ∀ x y : G, (x * y) ^ (k + 1) = x ^ (k + 1) * y ^ (k + 1)) :
      ∀ x y : G, y ^ k * x = x * y ^ k := by
    intro x y
    have e : (x ^ k * y ^ k) * (x * y) = (x ^ k * x) * (y ^ k * y) := by
      simpa only [pow_succ, hk x y] using hk1 x y
    simp only [mul_assoc] at e
    have e' : y ^ k * (x * y) = x * (y ^ k * y) := mul_left_cancel e
    rw [← mul_assoc, ← mul_assoc] at e'
    exact mul_right_cancel e'
  have central_n := central n hn hn1
  have hn2' : ∀ x y : G,
      (x * y) ^ ((n + 1) + 1) = x ^ ((n + 1) + 1) * y ^ ((n + 1) + 1) := by
    intro x y
    simpa only [Nat.add_assoc, Nat.reduceAdd] using hn2 x y
  have central_n1 := central (n + 1) hn1 hn2'
  have hcomm : a * b = b * a := by
    have c0 := central_n b a
    have c1 := central_n1 b a
    have c1' : (a ^ n * a) * b = b * (a ^ n * a) := by
      simpa only [pow_succ] using c1
    rw [← mul_assoc, ← c0] at c1'
    simp only [mul_assoc] at c1'
    exact mul_left_cancel c1'
  have hab : Commute a b := hcomm
  exact dummy_assumed a b (fun j => hab.mul_pow j) 0
