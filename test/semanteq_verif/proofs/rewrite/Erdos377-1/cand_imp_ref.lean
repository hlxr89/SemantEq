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
  obtain ⟨C, hC, hbound⟩ := _root_.erdos_377_assumed
  refine ⟨C, hC, fun n => ?_⟩
  rw [sumInvPrimesNotDvdCentralBinom, Nat.centralBinom_eq_two_mul_choose]
  apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_).trans
  · exact hbound n
  · intro p _ _
    by_cases hp : p ∣ (2 * n).choose n
    · rw [if_pos hp]
    · rw [if_neg hp]
      exact div_nonneg zero_le_one (Nat.cast_nonneg p)

end Erdos377
