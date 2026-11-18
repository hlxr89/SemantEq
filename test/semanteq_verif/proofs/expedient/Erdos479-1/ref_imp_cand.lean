import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

namespace Erdos479

-- ===== assumed statement (antecedent) =====
theorem erdos_479_assumed : ∀ᵉ (k : ℤ) (k ≠ 1),
    { n : ℕ | (2 : ℤ) ^ n ≡ k [ZMOD (n : ℤ)] }.Infinite := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_479_goal : ∀ᵉ (k > 1), { n | 2 ^ n ≡ k [MOD n]}.Infinite := by
  intro k hk
  have h := erdos_479_assumed 0 (k : ℤ) (by omega)
  exact h.mono (by
    intro n hn
    exact_mod_cast hn)

end Erdos479
