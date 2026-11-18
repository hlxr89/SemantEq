import Mathlib

namespace Erdos288

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem erdos_288_assumed :
    Set.Finite { I : Fin 2 → ℕ+ × ℕ+ |
    ∀ j, (I j).1 ≤ (I j).2 ∧
      ∃ n : ℕ+, (∑ j : Fin 2, ∑ nⱼ ∈ Set.Icc (I j).1 (I j).2, (nⱼ⁻¹ : ℚ)) = n } := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_288_goal :
    Set.Finite { I : Fin 2 → ℕ+ × ℕ+ |
    ∃ n : ℕ+, (∑ j : Fin 2, ∑ nⱼ ∈ Set.Icc (I j).1 (I j).2, (nⱼ⁻¹ : ℚ)) = n } := by
  -- not proved: dropping the interval-order condition makes the candidate set infinite
  sorry

end Erdos288
