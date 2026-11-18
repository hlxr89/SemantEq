import Mathlib

open Filter

namespace Erdos480

-- ===== unified context (both sides' local defs, merged) =====
-- Empty: neither preamble contains local definitions or structures.

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
  have hdiff (a b : ℕ) : |x a - x b| ≤ (1 : ℝ) := by
    rw [abs_le]
    constructor
    · rcases hx a with ⟨ha0, ha1⟩
      rcases hx b with ⟨hb0, hb1⟩
      linarith
    · rcases hx a with ⟨ha0, ha1⟩
      rcases hx b with ⟨hb0, hb1⟩
      linarith
  have h_bdd : BddBelow (Set.range fun n : ℕ =>
      atTop.liminf (fun m => n * |x (m + n) - x m|)) := by
    use 0
    rintro y ⟨n, rfl⟩
    apply Filter.le_liminf_of_le
    · apply Filter.isCoboundedUnder_ge_of_le atTop
      intro m
      calc
        (n : ℝ) * |x (m + n) - x m| ≤ (n : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (hdiff (m + n) m) (by positivity)
        _ = n := by simp
    · exact Filter.Eventually.of_forall fun m => by positivity
  calc
    ⨅ n, atTop.liminf (fun m => n * |x (m + n) - x m|) ≤
        atTop.liminf (fun m => (0 : ℕ) * |x (m + 0) - x m|) := by
          exact ciInf_le h_bdd 0
    _ = 0 := by simp
    _ ≤ 1 / √5 := by positivity

end Erdos480
