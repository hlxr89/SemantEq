import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
namespace Nat

def maxPrimeFac (n : ℕ) : ℕ := if n = 1 then 1 else n.primeFactorsList.getLastI

end Nat

namespace Erdos649

-- ===== assumed statement (antecedent) =====
theorem erdos_649_assumed :
    ¬ ∀ p q : ℕ, p.Prime → q.Prime →
      ∃ n : ℕ, n.maxPrimeFac = p ∧ (n + 1).maxPrimeFac = q := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_649_goal :
    ¬ ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
      ∃ n : ℕ, n.maxPrimeFac = p ∧ (n + 1).maxPrimeFac = q := by
  -- not proved: the candidate can fail only at p = q, which does not imply failure for distinct primes
  sorry

end Erdos649
