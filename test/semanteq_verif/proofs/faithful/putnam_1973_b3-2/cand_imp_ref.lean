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
  have hp_int : (p : ℤ) > 1 := by exact_mod_cast pgt1
  have hprime_int : ∀ x : ℤ, 0 < x ∧ x < (p : ℤ) →
      Nat.Prime (Int.natAbs (x^2 - x + (p : ℤ))) := by
    intro x hx
    have hx_nonneg : 0 ≤ x := le_of_lt hx.1
    have hx_cast : ((x.natAbs : ℕ) : ℤ) = x := Int.natAbs_of_nonneg hx_nonneg
    have hx_mem : x.natAbs ∈ Set.Ico 0 p := by
      constructor
      · exact Nat.zero_le _
      · have hlt : (x.natAbs : ℤ) < (p : ℤ) := by simpa [hx_cast] using hx.2
        exact_mod_cast hlt
    have h := hprime x.natAbs hx_mem
    have hx_sq : x.natAbs ≤ x.natAbs^2 := by nlinarith
    have hpoly : x^2 - x + (p : ℤ) =
        ((x.natAbs^2 - x.natAbs + p : ℕ) : ℤ) := by
      rw [Nat.cast_add, Nat.cast_sub hx_sq, hx_cast]
      norm_num
    rw [hpoly, Int.natAbs_natCast]
    exact h
  simpa using problem_statement_assumed (p : ℤ) hp_int hprime_int
