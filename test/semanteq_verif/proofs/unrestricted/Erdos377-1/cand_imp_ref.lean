import Mathlib

open Filter

open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
namespace Erdos377

noncomputable abbrev sumInvPrimesNotDvdCentralBinom (n : ℕ) : ℝ :=
  ∑ p ∈ Finset.Icc 1 n with p.Prime, if p ∣ n.centralBinom then 0 else (1 : ℝ) / p

end Erdos377

-- ===== assumed statement (antecedent) =====
theorem erdos_377_assumed : ∃ C > (0 : ℝ),
    ∀ (n : ℕ),
      ∑ p ∈ Finset.Icc 1 n, (if p ∣ (2 * n).choose n then 0 else (1 : ℝ) / p) ≤ C := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
namespace Erdos377

theorem erdos_377 :
    ∃ C > (0 : ℝ), ∀ (n : ℕ), sumInvPrimesNotDvdCentralBinom n ≤ C := by
  obtain ⟨C, hC, hbound⟩ := erdos_377_assumed
  refine ⟨C, hC, fun n ↦ ?_⟩
  apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_) (hbound n)
  intro p hp hnot
  split
  · exact le_rfl
  · positivity

end Erdos377
