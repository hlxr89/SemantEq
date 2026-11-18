import Mathlib

open scoped ArithmeticFunction.sigma

-- ===== unified context (both sides' local defs, merged) =====
-- empty

namespace Erdos826

-- ===== assumed statement (antecedent) =====
theorem erdos_826_assumed :
    { n | ∃ C > (0 : ℝ),
    ∀ k ≥ 1, σ 0 (n + k) ≤ C * k }.Infinite := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_826_goal :
    ∃ C > (0 : ℝ), { n | ∀ k ≥ 1, σ 0 (n + k) ≤ C * k }.Infinite := by
  -- not proved: pointwise existential constants cannot in general be made uniform on an infinite subset
  sorry

end Erdos826
