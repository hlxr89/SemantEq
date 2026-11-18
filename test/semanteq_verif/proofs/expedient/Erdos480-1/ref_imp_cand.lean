import Mathlib

namespace Erdos480

open Filter

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem erdos_480_assumed :
    ∀ (x : ℕ → ℝ), (∀ n, x n ∈ Set.Icc 0 1) →
    ⨅ (n : ℕ+), atTop.liminf (fun m => (n : ℕ) * |x (m + (n : ℕ)) - x m|) ≤ 1 / √5 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_480_goal :
    ∀ (x : ℕ → ℝ), (∀ n, x n ∈ Set.Icc 0 1) →
    ⨅ n, atTop.liminf (fun m => n * |x (m + n) - x m|) ≤ 1 / √5 := by
  intro x hx
  calc
    ⨅ n, atTop.liminf (fun m => n * |x (m + n) - x m|) ≤
        atTop.liminf (fun m => (0 : ℕ) * |x (m + 0) - x m|) := by
      apply ciInf_le
      refine ⟨0, ?_⟩
      rintro y ⟨n, rfl⟩
      apply Filter.le_liminf_of_le
      · apply Filter.isCoboundedUnder_ge_of_le atTop (x := (n : ℝ))
        intro m
        have h : |x (m + n) - x m| ≤ (1 : ℝ) := by
          rcases hx (m + n) with ⟨ha0, ha1⟩
          rcases hx m with ⟨hb0, hb1⟩
          rw [abs_sub_le_iff]
          constructor <;> linarith
        simpa only [mul_one] using mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n)
      · exact
        Filter.Eventually.of_forall fun m ↦ mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
    _ = 0 := by simp
    _ ≤ 1 / √5 := by positivity

end Erdos480
