import Mathlib

open Filter

open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
namespace Erdos377

noncomputable abbrev sumInvPrimesNotDvdCentralBinom (n : ℕ) : ℝ :=
  ∑ p ∈ Finset.Icc 1 n with p.Prime, if p ∣ n.centralBinom then 0 else (1 : ℝ) / p

-- ===== assumed statement (antecedent) =====
theorem erdos_377_assumed :
    ∃ C > (0 : ℝ), ∀ (n : ℕ), sumInvPrimesNotDvdCentralBinom n ≤ C := by
  sorry

end Erdos377

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_377 : ∃ C > (0 : ℝ),
    ∀ (n : ℕ),
      ∑ p ∈ Finset.Icc 1 n, (if p ∣ (2 * n).choose n then 0 else (1 : ℝ) / p) ≤ C := by
  -- not proved: at n = 3^k every multiple of 3 contributes, giving an unbounded harmonic subsum
  sorry
