import Mathlib

open Filter

namespace Erdos266

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem erdos_266_assumed (a : ℕ → ℕ) :
    ¬ ((∀ n : ℕ, a n ≥ 1) ∧ Summable ((1 : ℝ) / a ·) →
      ∃ t ≥ (1 : ℕ), Irrational <| ∑' n, (1 : ℝ) / ((a n) + t)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_266 :
    ¬ ∀ (a : ℕ → ℕ), ((∀ n : ℕ, a n ≥ 1) ∧ Summable ((1 : ℝ) / a ·) →
      ∃ t ≥ (1 : ℕ), Irrational <| ∑' n, (1 : ℝ) / ((a n) + t)) := by
  intro h
  exact erdos_266_assumed (fun _ => 0) (h (fun _ => 0))

end Erdos266
