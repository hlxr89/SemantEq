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
  exfalso
  obtain ⟨a, ha⟩ := erdos_689_assumed 3 (by omega)
  have h1 := ha 1 (by simp)
  have h2 := ha 2 (by simp)
  have hi : Finset.Icc 1 3 = {1, 2, 3} := by native_decide
  rw [hi] at h1 h2
  norm_num [Finset.filter_insert, Finset.filter_singleton] at h1 h2
  have ha1 : a 2 ≡ 1 [MOD 2] := by
    by_contra hn
    rw [if_neg hn] at h1
    split at h1 <;> simp_all
  have ha2 : a 2 ≡ 2 [MOD 2] := by
    by_contra hn
    rw [if_neg hn] at h2
    split at h2 <;> simp_all
  norm_num [Nat.ModEq] at ha1 ha2
  omega

end Erdos689
