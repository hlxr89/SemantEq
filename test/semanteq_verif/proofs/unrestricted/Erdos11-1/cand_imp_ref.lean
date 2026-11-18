import Mathlib

open Filter

-- ===== unified context (both sides' local defs, merged) =====
-- empty

namespace Erdos11

-- ===== assumed statement (antecedent) =====
theorem erdos_11_assumed (n : ℕ) (hn : Odd n) :
    ∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_11 :
    ∀ᶠ n : ℕ in atTop, Odd n → ∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l := by
  exact Filter.Eventually.of_forall fun n hn => erdos_11_assumed n hn

end Erdos11
