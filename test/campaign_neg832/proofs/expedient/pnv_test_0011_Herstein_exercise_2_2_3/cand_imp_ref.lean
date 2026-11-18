import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] (a b : G) (i : ℤ) (h : ∀ j ∈ ({i-1, i, i+1} : Finset ℤ), (a*b)^j = a^j * b^j) : Commute a b := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_2_3 {G : Type*} [Group G]
  {P : ℕ → Prop} {hP : P = λ i => ∀ a b : G, (a*b)^i = a^i * b^i}
  (hP1 : ∃ n : ℕ, P n ∧ P (n+1) ∧ P (n+2)) : 
  ∀ a b : G, a*b = b*a := by
  obtain ⟨n, hn, hn1, hn2⟩ := hP1
  rw [hP] at hn hn1 hn2
  intro a b
  apply Commute.eq
  apply dummy_assumed a b ((n : ℤ) + 1)
  intro j hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with hj | hj | hj
  · subst j
    simpa using hn a b
  · subst j
    have hz : (a * b) ^ ((n + 1 : ℕ) : ℤ) =
        a ^ ((n + 1 : ℕ) : ℤ) * b ^ ((n + 1 : ℕ) : ℤ) := by
      simpa only [zpow_natCast] using hn1 a b
    convert hz using 1 <;> norm_num
  · subst j
    have hz : (a * b) ^ ((n + 2 : ℕ) : ℤ) =
        a ^ ((n + 2 : ℕ) : ℤ) * b ^ ((n + 2 : ℕ) : ℤ) := by
      simpa only [zpow_natCast] using hn2 a b
    convert hz using 1 <;> norm_num
