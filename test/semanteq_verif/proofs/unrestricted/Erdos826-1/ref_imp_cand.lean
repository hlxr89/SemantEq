import Mathlib

open scoped ArithmeticFunction.sigma

namespace Erdos826

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem erdos_826_assumed :
    ∃ C > (0 : ℝ), { n | ∀ k ≥ 1, σ 0 (n + k) ≤ C * k }.Infinite := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_826_goal :
    { n | ∃ C > (0 : ℝ),
    ∀ k ≥ 1, σ 0 (n + k) ≤ C * k }.Infinite := by
  obtain ⟨C, hC, hInfinite⟩ := erdos_826_assumed
  apply hInfinite.mono
  intro n hn
  exact ⟨C, hC, hn⟩

end Erdos826
