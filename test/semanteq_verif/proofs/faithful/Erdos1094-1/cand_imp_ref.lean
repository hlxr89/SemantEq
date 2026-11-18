import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

namespace Erdos1094

-- ===== assumed statement (antecedent) =====
theorem erdos_1094_assumed :
    {(n, k) : ℕ × ℕ | 2 * k ≤ n ∧ (n.choose k).minFac > max (n / k) k}.Finite := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_1094 :
    {(n, k) : ℕ × ℕ | 0 < k ∧ 2 * k ≤ n ∧ (n.choose k).minFac > max (n / k) k}.Finite := by
  apply erdos_1094_assumed.subset
  rintro ⟨n, k⟩ ⟨_, hle, hfac⟩
  exact ⟨hle, hfac⟩

end Erdos1094
