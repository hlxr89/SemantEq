import Mathlib

open scoped ArithmeticFunction.sigma

namespace Erdos826

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem erdos_826_assumed :
    { n | ∃ C > (0 : ℝ),
    ∀ k ≥ 1, σ 0 (n + k) ≤ C * k }.Infinite := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_826 :
    ∃ C > (0 : ℝ), { n | ∀ k ≥ 1, σ 0 (n + k) ≤ C * k }.Infinite := by
  -- not proved: the antecedent allows its witness C to depend on n, so it does not provide a uniform C on an infinite set
  sorry

end Erdos826
