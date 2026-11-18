import Mathlib

open ArithmeticFunction.sigma

-- ===== unified context (both sides' local defs, merged) =====
-- empty

namespace Erdos412

-- ===== assumed statement (antecedent) =====
theorem erdos_412_assumed :
    ∀ᵉ (m ≥ 2) (n ≥ 2), ∃ i j, (σ 1)^[i] m = (σ 1)^[j] n := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_412_goal (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∃ i j, σ i m = σ j n := by
  -- not proved: the candidate is false at m = 2 and n = 6, while the reference is an open conjecture
  sorry

end Erdos412
