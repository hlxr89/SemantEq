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
theorem erdos_480_goal :
    ∀ (x : ℕ → ℝ), (∀ n, x n ∈ Set.Icc 0 1) →
    ⨅ n, atTop.liminf (fun m => n * |x (m + n) - x m|) ≤ 1 / √5 := by
  intro x hx
  have hnonneg (n : ℕ) :
      0 ≤ atTop.liminf (fun m => n * |x (m + n) - x m|) := by
    have hupper :
        IsBoundedUnder (· ≤ ·) atTop (fun (m : ℕ) => (n : ℝ) * |x (m + n) - x m|) := by
      change ∃ b : ℝ, ∀ᶠ m : ℕ in atTop, (n : ℝ) * |x (m + n) - x m| ≤ b
      refine ⟨(n : ℝ), Eventually.of_forall fun (m : ℕ) => ?_⟩
      have habs : |x (m + n) - x m| ≤ 1 := by
        apply abs_le.mpr
        constructor
        · simpa only [zero_sub] using sub_le_sub (hx (m + n)).1 (hx m).2
        · simpa only [sub_zero] using sub_le_sub (hx (m + n)).2 (hx m).1
      simpa only [mul_one] using mul_le_mul_of_nonneg_left habs (Nat.cast_nonneg n)
    apply le_liminf_of_le hupper.isCoboundedUnder_ge
    exact Eventually.of_forall fun m => mul_nonneg (Nat.cast_nonneg n) (abs_nonneg _)
  have hbdd :
      BddBelow (Set.range fun n : ℕ =>
        atTop.liminf (fun m => n * |x (m + n) - x m|)) := by
    rw [bddBelow_def]
    exact ⟨0, fun _ ⟨n, hn⟩ => hn ▸ hnonneg n⟩
  have hbridge :
      (⨅ n : ℕ, atTop.liminf (fun m => n * |x (m + n) - x m|)) ≤
      ⨅ n : ℕ+, atTop.liminf (fun m => (n : ℕ) * |x (m + (n : ℕ)) - x m|) := by
    refine le_ciInf fun (n : ℕ+) => ?_
    exact ciInf_le hbdd (n : ℕ)
  exact hbridge.trans (erdos_480_assumed x hx)

end Erdos480
