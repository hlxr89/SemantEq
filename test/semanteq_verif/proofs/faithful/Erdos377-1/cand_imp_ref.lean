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
  rcases erdos_377_assumed with ⟨C, hC, hbound⟩
  refine ⟨C, hC, fun n => ?_⟩
  calc
    sumInvPrimesNotDvdCentralBinom n ≤
        ∑ p ∈ Finset.Icc 1 n,
          (if p ∣ (2 * n).choose n then 0 else (1 : ℝ) / p) := by
      unfold sumInvPrimesNotDvdCentralBinom
      rw [← Nat.centralBinom_eq_two_mul_choose]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        simp only [Finset.mem_filter] at hp
        exact hp.1
      · intro p hpIcc hpNotPrime
        split
        · exact le_rfl
        · positivity
    _ ≤ C := hbound n

end Erdos377
