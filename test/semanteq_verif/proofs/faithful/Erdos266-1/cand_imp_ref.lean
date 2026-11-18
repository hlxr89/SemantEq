import Mathlib

open Filter

-- ===== unified context (both sides' local defs, merged) =====
-- empty

namespace Erdos266

-- ===== assumed statement (antecedent) =====
theorem erdos_266_assumed (a : ℕ → ℕ) :
    ¬ ((∀ n : ℕ, a n ≥ 1) ∧ Summable ((1 : ℝ) / a ·) →
      ∃ t ≥ (1 : ℕ), Irrational <| ∑' n, (1 : ℝ) / ((a n) + t)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_266_goal :
    ¬ ∀ (a : ℕ → ℕ), ((∀ n : ℕ, a n ≥ 1) ∧ Summable ((1 : ℝ) / a ·) →
      ∃ t ≥ (1 : ℕ), Irrational <| ∑' n, (1 : ℝ) / ((a n) + t)) := by
  intro h
  exact erdos_266_assumed (fun _ => 1) (h (fun _ => 1))

end Erdos266
