import Mathlib

open Nat Set MeasureTheory Topology Filter

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (p : ℤ) (hp : p > 1) 
  (h_prime : ∀ x : ℤ, 0 < x ∧ x < p → Nat.Prime (Int.natAbs (x^2 - x + p))) :
  ∃! triple : ℤ × ℤ × ℤ, 
    let (a, b, c) := triple
    b^2 - 4*a*c = 1 - 4*p ∧ 0 < a ∧ a ≤ c ∧ -a ≤ b ∧ b < a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1973_b3
(p : ℕ)
(pgt1 : p > 1)
(hprime : ∀ x ∈ Set.Ico 0 p, Nat.Prime (x^2 - x + p))
: ∃! triple : ℤ × ℤ × ℤ, let (a,b,c) := triple; b^2 - 4*a*c = 1 - 4*p ∧ 0 < a ∧ a ≤ c ∧ -a ≤ b ∧ b < a := by
  apply problem_statement_assumed (p : ℤ) (by omega)
  intro x hx
  have hx0 : 0 ≤ x := by omega
  have hxn : ((x.natAbs : ℕ) : ℤ) = x := by simp [Int.natAbs_of_nonneg hx0]
  have h := hprime x.natAbs (by constructor <;> omega)
  rw [← hxn]
  have hnpos : x.natAbs ≠ 0 := by omega
  have hnle : x.natAbs ≤ x.natAbs ^ 2 := by
    nlinarith [Nat.one_le_iff_ne_zero.mpr hnpos]
  have hnonneg : 0 ≤ ((x.natAbs : ℕ) : ℤ) ^ 2 - x.natAbs + p := by
    have : 0 ≤ ((x.natAbs ^ 2 - x.natAbs : ℕ) : ℤ) := by positivity
    rw [Nat.cast_sub hnle] at this
    positivity
  have hcast : ((x.natAbs ^ 2 - x.natAbs + p : ℕ) : ℤ) =
      ((x.natAbs : ℕ) : ℤ) ^ 2 - x.natAbs + p := by
    push_cast [Nat.cast_sub hnle]
    ring
  have heq : Int.natAbs (((x.natAbs : ℕ) : ℤ) ^ 2 - x.natAbs + p) =
      x.natAbs ^ 2 - x.natAbs + p := by
    omega
  rw [heq]
  exact h
