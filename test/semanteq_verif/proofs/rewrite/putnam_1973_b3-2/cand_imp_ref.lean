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
: ∃! triple : ℤ × ℤ × ℤ, let (a,b,c) := triple; b^2 - 4*a*c = 1 - 4*p ∧ 0 < a ∧ a ≤ c ∧ -a ≤ b ∧ b < a :=
by
  have hp_int : (p : ℤ) > 1 := by
    exact_mod_cast pgt1
  have hprime_int : ∀ x : ℤ, 0 < x ∧ x < (p : ℤ) →
      Nat.Prime (Int.natAbs (x^2 - x + (p : ℤ))) := by
    intro x hx
    have hx_nonneg : 0 ≤ x := le_of_lt hx.1
    have hx_cast : ((x.natAbs : ℕ) : ℤ) = x := by
      rw [Int.natCast_natAbs, abs_of_nonneg hx_nonneg]
    have hx_lt : x.natAbs < p := by
      rw [← Nat.cast_lt (α := ℤ), hx_cast]
      exact hx.2
    have hx_prime := hprime x.natAbs ⟨Nat.zero_le _, hx_lt⟩
    have hpoly : ((x.natAbs^2 - x.natAbs + p : ℕ) : ℤ) =
        x^2 - x + (p : ℤ) := by
      rw [Nat.cast_add, Nat.cast_sub (Nat.le_pow Nat.zero_lt_two),
        Nat.cast_pow, hx_cast]
    rw [← hpoly, Int.natAbs_natCast]
    exact hx_prime
  exact problem_statement_assumed (p : ℤ) hp_int hprime_int
