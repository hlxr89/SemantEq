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
  intro _ k hk
  rcases lt_trichotomy k 0 with hneg | rfl | hpos
  · -- not proved: the candidate only covers positive residues, while this case has k < 0
    sorry
  · refine (Set.infinite_range_of_injective (f := fun m : ℕ => 2 ^ (m + 1)) ?_).mono ?_
    · exact (Nat.pow_right_injective (by omega : 2 ≤ 2)).comp Nat.succ_injective
    · rintro n ⟨m, rfl⟩
      simp only [Set.mem_setOf_eq]
      rw [Int.modEq_iff_dvd]
      norm_num only [Nat.cast_ofNat, Nat.cast_pow, sub_zero, zero_sub]
      apply dvd_neg.mpr
      apply pow_dvd_pow
      induction m with
      | zero => norm_num
      | succ m ih =>
          rw [pow_succ]
          omega
  · have hgt : 1 < k.natAbs := by
      have habs : (k.natAbs : ℤ) = k := Int.natAbs_of_nonneg hpos.le
      have h : (1 : ℤ) < (k.natAbs : ℤ) := by omega
      exact_mod_cast h
    have habs : (k.natAbs : ℤ) = k := Int.natAbs_of_nonneg hpos.le
    have h := erdos_479_assumed k.natAbs hgt
    exact h.mono (by
      intro n hn
      rw [← habs]
      exact_mod_cast hn)

end Erdos479
