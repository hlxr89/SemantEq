import Mathlib

open ArithmeticFunction.sigma

namespace Erdos412

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem erdos_412_assumed :
    ∀ᵉ (m ≥ 2) (n ≥ 2), ∃ i j, (σ 1)^[i] m = (σ 1)^[j] n := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_412 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∃ i j, σ i m = σ j n := by
  -- not proved: iterates of σ 1 are not the exponent-indexed functions σ i, and the candidate statement is false (for example, m = 2 and n = 6)
  sorry

end Erdos412
