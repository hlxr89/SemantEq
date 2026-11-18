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
  have hk1 : (k : ℤ) ≠ 1 := by omega
  have h := erdos_479_assumed 0 (k : ℤ) hk1
  have hpow (n : ℕ) : (2 : ℤ) ^ n = ((2 ^ n : ℕ) : ℤ) := by norm_num
  simp_rw [hpow] at h
  simpa only [Int.natCast_modEq_iff] using h

end Erdos479
