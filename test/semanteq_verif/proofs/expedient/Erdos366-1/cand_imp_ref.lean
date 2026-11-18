import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
namespace Nat

def Full (k : ℕ) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p^k ∣ n

end Nat

namespace Erdos366

-- ===== assumed statement (antecedent) =====
theorem erdos_366_assumed :
    ∃ (n : ℕ), (2).Full n ∧ (3).Full (n + 1) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_366_goal :
    ∃ n > 0, (2).Full n ∧ (3).Full (n + 1) := by
  -- not proved: the antecedent has the trivial witness n = 0, while the positive conclusion is open Erdős problem 366
  sorry

end Erdos366
