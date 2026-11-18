import Mathlib

open Filter

namespace Erdos480

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem erdos_480_assumed :
    ∀ (x : ℕ → ℝ), (∀ n, x n ∈ Set.Icc 0 1) →
    ⨅ n, atTop.liminf (fun m => n * |x (m + n) - x m|) ≤ 1 / √5 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_480_goal :
    ∀ (x : ℕ → ℝ), (∀ n, x n ∈ Set.Icc 0 1) →
    ⨅ (n : ℕ+), atTop.liminf (fun m => (n : ℕ) * |x (m + (n : ℕ)) - x m|) ≤ 1 / √5 := by
  -- not proved: the assumed infimum ranges over all naturals and is weakened by its zero-index term, so it gives no bound on the positive-natural infimum
  sorry

end Erdos480
