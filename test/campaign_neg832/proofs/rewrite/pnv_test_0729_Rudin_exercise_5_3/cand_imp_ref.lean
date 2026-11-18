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
  have hMnonneg : 0 ≤ M := le_trans (abs_nonneg (deriv g 0)) (hM 0)
  have hden : 0 < M + 1 := add_pos_of_nonneg_of_pos hMnonneg zero_lt_one
  refine ⟨1 / (M + 1), ?_⟩
  intro ε hεpos hεN
  have hbdd : ∀ x, ‖deriv g x‖ ≤ M := by
    intro x
    simpa only [Real.norm_eq_abs] using hM x
  have hprod : ε * (M + 1) < 1 := (lt_div_iff₀ hden).mp hεN
  have hsmall : ε * M < 1 :=
    lt_trans (mul_lt_mul_of_pos_left (lt_add_of_pos_right M zero_lt_one) hεpos) hprod
  exact dummy_assumed g hbdd ε hsmall
