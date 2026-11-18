import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

namespace Erdos1094

-- ===== assumed statement (antecedent) =====
theorem erdos_1094_assumed :
    {(n, k) : ℕ × ℕ | 2 * k ≤ n ∧ (n.choose k).minFac > max (n / k) k}.Finite := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_1094_goal :
    {(n, k) : ℕ × ℕ | 0 < k ∧ 2 * k ≤ n ∧ (n.choose k).minFac > max (n / k) k}.Finite := by
  exact erdos_1094_assumed.subset fun _ h => h.2

end Erdos1094
