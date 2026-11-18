import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

namespace Erdos288

-- ===== assumed statement (antecedent) =====
theorem erdos_288_assumed :
    Set.Finite { I : Fin 2 → ℕ+ × ℕ+ |
    ∃ n : ℕ+, (∑ j : Fin 2, ∑ nⱼ ∈ Set.Icc (I j).1 (I j).2, (nⱼ⁻¹ : ℚ)) = n } := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_288_goal :
    Set.Finite { I : Fin 2 → ℕ+ × ℕ+ |
    ∀ j, (I j).1 ≤ (I j).2 ∧
      ∃ n : ℕ+, (∑ j : Fin 2, ∑ nⱼ ∈ Set.Icc (I j).1 (I j).2, (nⱼ⁻¹ : ℚ)) = n } := by
  apply erdos_288_assumed.subset
  intro I hI
  exact (hI 0).2

end Erdos288
