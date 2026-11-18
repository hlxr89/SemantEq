import Mathlib

open Filter

namespace Erdos266

-- ===== unified context (both sides' local defs, merged) =====
-- The unified context is empty.

-- ===== assumed statement (antecedent) =====
theorem erdos_266_assumed (a : ℕ → ℕ) :
    ¬ ((∀ n : ℕ, a n ≥ 1) ∧ Summable ((1 : ℝ) / a ·) →
      ∃ t ≥ (1 : ℕ), Irrational <| ∑' n, (1 : ℝ) / ((a n) + t)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_266_goal :
    ¬ ∀ (a : ℕ → ℕ), ((∀ n : ℕ, a n ≥ 1) ∧ Summable ((1 : ℝ) / a ·) →
      ∃ t ≥ (1 : ℕ), Irrational <| ∑' n, (1 : ℝ) / ((a n) + t)) := by
  exfalso
  apply erdos_266_assumed (fun _ => 0)
  intro h
  exact (Nat.not_succ_le_zero 0 (h.1 0)).elim

end Erdos266
