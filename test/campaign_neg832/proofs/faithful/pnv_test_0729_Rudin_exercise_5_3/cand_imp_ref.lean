import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (g : ℝ → ℝ) (hbdd : ∀ x, ‖deriv g x‖ ≤ M) (ε : ℝ) (hε : ε * M < 1) : Function.Injective fun x => x + ε * g x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_3 {g : ℝ → ℝ} (hg : Continuous g)
  (hg' : ∃ M : ℝ, ∀ x : ℝ, |deriv g x| ≤ M) :
  ∃ N, ∀ ε > 0, ε < N → Function.Injective (λ x : ℝ => x + ε * g x) := by
  rcases hg' with ⟨M, hM⟩
  refine ⟨1 / (|M| + 1), ?_⟩
  intro ε hε hεN
  have hbdd : ∀ x, ‖deriv g x‖ ≤ M := by
    intro x
    simpa [Real.norm_eq_abs] using hM x
  apply dummy_assumed (M := M) g hbdd ε
  have hden : 0 < |M| + 1 := by positivity
  have hprod : ε * (|M| + 1) < 1 := (lt_div_iff₀ hden).mp hεN
  have hMle : M ≤ |M| := le_abs_self M
  nlinarith
