import Mathlib

open Filter

namespace Erdos480

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem erdos_480_assumed :
    ∀ (x : ℕ → ℝ), (∀ n, x n ∈ Set.Icc 0 1) →
    ⨅ (n : ℕ+), atTop.liminf (fun m => (n : ℕ) * |x (m + (n : ℕ)) - x m|) ≤ 1 / √5 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_480 :
    ∀ (x : ℕ → ℝ), (∀ n, x n ∈ Set.Icc 0 1) →
    ⨅ n, atTop.liminf (fun m => n * |x (m + n) - x m|) ≤ 1 / √5 := by
  intro x hx
  have hnonneg (n : ℕ) :
      0 ≤ atTop.liminf (fun m => n * |x (m + n) - x m|) := by
    apply le_liminf_of_le
    · apply Filter.IsCoboundedUnder.of_frequently_le (a := (n : ℝ))
      apply (Filter.Eventually.of_forall fun m => ?_).frequently
      have hdiff : |x (m + n) - x m| ≤ 1 := by
        rw [abs_le]
        constructor
        · linarith [(hx (m + n)).1, (hx m).2]
        · linarith [(hx (m + n)).2, (hx m).1]
      exact mul_le_of_le_one_right (Nat.cast_nonneg n) hdiff
    · filter_upwards with m
      positivity
  have hbdd : BddBelow (Set.range
      (fun n : ℕ => atTop.liminf (fun m => n * |x (m + n) - x m|))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hnonneg n
  have hindex :
      (⨅ n : ℕ, atTop.liminf (fun m => n * |x (m + n) - x m|)) ≤
        ⨅ n : ℕ+, atTop.liminf
          (fun m => (n : ℕ) * |x (m + (n : ℕ)) - x m|) := by
    refine le_ciInf fun n => ?_
    exact ciInf_le hbdd (n : ℕ)
  exact hindex.trans (erdos_480_assumed x hx)

end Erdos480
