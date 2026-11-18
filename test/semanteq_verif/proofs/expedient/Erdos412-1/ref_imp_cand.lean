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
  -- not proved: the candidate is false at m = 3, n = 4, while the antecedent is the open Erdős 412 conjecture.
  sorry

end Erdos412
