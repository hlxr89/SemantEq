import Mathlib

open Real Filter

open scoped Finset

namespace Erdos510

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem erdos_510_assumed :
    ∃ (c : ℝ) (hc : 0 < c),
      ∀ (N : ℕ), ∀ (A : Finset ℤ), # A = N →
      (∃ (θ : ℝ), (∑ n ∈ A, (n * θ).cos) < -c * (N : ℝ).sqrt) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_510_goal :
    ∃ (c : ℝ) (hc : 0 < c),
      ∀ᶠ N in atTop, ∀ (A : Finset ℕ), 0 ∉ A → #A = N →
      ∃ θ, ∑ n ∈ A, cos (n * θ) < -c * sqrt N := by
  rcases erdos_510_assumed with ⟨c, hc, h⟩
  rcases h 0 ∅ (by simp) with ⟨θ, hθ⟩
  norm_num at hθ

end Erdos510
