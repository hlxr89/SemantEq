import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

namespace Erdos479

-- ===== assumed statement (antecedent) =====
theorem erdos_479_assumed : ∀ᵉ (k > 1), { n | 2 ^ n ≡ k [MOD n]}.Infinite := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_479_goal : ∀ᵉ (k : ℤ) (k ≠ 1),
    { n : ℕ | (2 : ℤ) ^ n ≡ k [ZMOD (n : ℤ)] }.Infinite := by
  -- not proved: the antecedent covers only natural k > 1, not integer k ≤ 0
  sorry

end Erdos479
