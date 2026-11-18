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
  have hk_ne : k ≠ 1 := ne_of_gt hk
  have hk_int_ne : (k : ℤ) ≠ 1 := by
    exact_mod_cast hk_ne
  have h := erdos_479_assumed (0 : ℤ) (k : ℤ) hk_int_ne
  apply h.mono
  intro n hn
  apply Int.natCast_modEq_iff.mp
  simpa only [Nat.cast_ofNat, Nat.cast_pow] using hn

end Erdos479
