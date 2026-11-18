import Mathlib

-- No `open` or `open scoped` lines occur in either input file.

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
theorem erdos_366 :
    ∃ n > 0, (2).Full n ∧ (3).Full (n + 1) := by
  -- not proved: the candidate admits the vacuous witness n = 0 and does not imply positivity
  sorry

end Erdos366
