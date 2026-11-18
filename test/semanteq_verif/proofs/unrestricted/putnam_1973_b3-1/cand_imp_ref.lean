import Mathlib
open Nat Set MeasureTheory Topology Filter

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (p : ℕ) (hp : p > 1) 
  (h : ∀ x : ℕ, 0 < x → x < p → Nat.Prime (x^2 - x + p)) :
  ∃! t : ℤ × ℤ × ℤ, 
    let (a, b, c) := t
    b^2 - 4*a*c = 1 - 4*p ∧ 
    0 < a ∧ a ≤ c ∧ 
    -a ≤ b ∧ b < a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1973_b3
(p : ℕ)
(pgt1 : p > 1)
(hprime : ∀ x ∈ Set.Ico 0 p, Nat.Prime (x^2 - x + p))
: ∃! triple : ℤ × ℤ × ℤ, let (a,b,c) := triple; b^2 - 4*a*c = 1 - 4*p ∧ 0 < a ∧ a ≤ c ∧ -a ≤ b ∧ b < a := by
  apply problem_statement_assumed p pgt1
  intro x hxpos hxp
  exact hprime x ⟨Nat.zero_le x, hxp⟩
