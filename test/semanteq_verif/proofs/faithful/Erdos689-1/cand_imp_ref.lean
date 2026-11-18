import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

namespace Erdos689

-- ===== assumed statement (antecedent) =====
theorem erdos_689_assumed :
    ∀ n ≥ 3, ∃ a : ℕ → ℕ, ∀ m ∈ Finset.Icc 1 n,
      2 ≤ (Finset.Icc 1 n |>.filter fun p => p.Prime ∧ a p ≡ m [MOD p]).card := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_689_goal :
    ∀ᶠ n in .atTop, ∃ a : ℕ → ℕ, ∀ m ∈ Finset.Icc 1 n,
      2 ≤ (Finset.Icc 1 n |>.filter fun p => p.Prime ∧ a p ≡ m [MOD p]).card := by
  filter_upwards [Filter.eventually_ge_atTop (3 : ℕ)] with n hn
  exact erdos_689_assumed n hn

end Erdos689
