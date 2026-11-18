import Mathlib

open Real Filter

open scoped Finset

namespace Erdos510

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem erdos_510_assumed :
    ∃ (c : ℝ) (hc : 0 < c),
      ∀ᶠ N in atTop, ∀ (A : Finset ℕ), 0 ∉ A → #A = N →
      ∃ θ, ∑ n ∈ A, cos (n * θ) < -c * sqrt N := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_510_goal :
    ∃ (c : ℝ) (hc : 0 < c),
      ∀ (N : ℕ), ∀ (A : Finset ℤ), # A = N →
      (∃ (θ : ℝ), (∑ n ∈ A, (n * θ).cos) < -c * (N : ℝ).sqrt) := by
  -- not proved: the candidate is false for N = 1 and A = {0}, while the reference is an open conjecture.
  sorry

end Erdos510
