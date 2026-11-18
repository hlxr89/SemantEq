import Mathlib

namespace Erdos386

open Nat

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem erdos_386_assumed :
    ∃ᶠ n in .atTop, ∃ k ≥ 2,
      k ≤ n - 2 ∧ ∃ p q : ℕ, n.choose k = ∏ i ∈ .Ico p q, nth Nat.Prime i := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_386_goal :
    ∃ k ≥ 2, ∃ᶠ n in .atTop,
      k ≤ n - 2 ∧ ∃ p q : ℕ, n.choose k = ∏ i ∈ .Ico p q, nth Nat.Prime i := by
  -- not proved: swapping an unbounded existential with `Frequently` is not valid in general
  sorry

end Erdos386
