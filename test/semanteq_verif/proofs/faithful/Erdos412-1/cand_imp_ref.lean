import Mathlib
open ArithmeticFunction.sigma

namespace Erdos412

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem erdos_412_assumed (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∃ i j, σ i m = σ j n := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_412_goal :
    ∀ᵉ (m ≥ 2) (n ≥ 2), ∃ i j, (σ 1)^[i] m = (σ 1)^[j] n := by
  -- not proved: the candidate's exponent-indexed sigma values do not re-express iterates of σ 1; only an impermissible ex-falso route is available from its false universal claim
  sorry
end Erdos412
