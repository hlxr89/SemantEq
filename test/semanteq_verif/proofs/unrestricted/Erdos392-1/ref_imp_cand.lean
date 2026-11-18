import Mathlib

open Filter

open scoped Nat

-- ===== unified context (both sides' local defs, merged) =====
-- empty

namespace Erdos392

-- ===== assumed statement (antecedent) =====
theorem erdos_392_assumed (A : ℕ → ℕ) (h : ∀ n > 0,
    IsLeast { t + 1 | (t) (_ : ∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧
      Monotone a ∧ a (Fin.last t) ≤ n ^ 2) } (A n)) :
    ((fun (n : ℕ) => (A n - n / 2 + n / (2 * Real.log n) : ℝ)) =o[atTop] fun n => n / Real.log n) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_392 (A : ℕ → ℕ) (h : ∀ n,
    IsLeast { t + 1 | (t) (_ : ∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧
      Monotone a ∧ a (Fin.last t) ≤ n ^ 2) } (A n)) :
    ((fun (n : ℕ) => (A n - n / 2 + n / (2 * Real.log n) : ℝ)) =o[atTop] fun n => n / Real.log n) := by
  apply erdos_392_assumed A
  intro n hn
  exact h n

end Erdos392
