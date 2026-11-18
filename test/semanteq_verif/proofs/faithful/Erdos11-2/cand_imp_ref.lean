import Mathlib

open Filter

-- ===== unified context (both sides' local defs, merged) =====
-- empty

namespace Erdos11

-- ===== assumed statement (antecedent) =====
theorem erdos_11_assumed (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    ∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_11_goal :
    ∀ᶠ n : ℕ in atTop, Odd n → ∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l := by
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn'
  exact fun hn => erdos_11_assumed n hn hn'

end Erdos11
