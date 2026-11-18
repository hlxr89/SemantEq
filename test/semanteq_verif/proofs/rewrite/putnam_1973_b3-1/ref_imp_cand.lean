import Mathlib

open Nat Set MeasureTheory Topology Filter

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem putnam_1973_b3_assumed
(p : ℕ)
(pgt1 : p > 1)
(hprime : ∀ x ∈ Set.Ico 0 p, Nat.Prime (x^2 - x + p))
: ∃! triple : ℤ × ℤ × ℤ, let (a,b,c) := triple; b^2 - 4*a*c = 1 - 4*p ∧ 0 < a ∧ a ≤ c ∧ -a ≤ b ∧ b < a :=
by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (p : ℕ) (hp : p > 1) 
  (h : ∀ x : ℕ, 0 < x → x < p → Nat.Prime (x^2 - x + p)) :
  ∃! t : ℤ × ℤ × ℤ, 
    let (a, b, c) := t
    b^2 - 4*a*c = 1 - 4*p ∧ 
    0 < a ∧ a ≤ c ∧ 
    -a ≤ b ∧ b < a := by
  apply putnam_1973_b3_assumed p hp
  intro x hx
  rcases hx with ⟨_, hxp⟩
  rcases x.eq_zero_or_pos with rfl | hxpos
  · simpa only [pow_two, zero_mul, Nat.zero_sub, zero_add, one_mul,
      Nat.sub_self] using h 1 Nat.zero_lt_one hp
  · exact h x hxpos hxp
