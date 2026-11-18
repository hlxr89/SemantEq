import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- Empty: neither preamble contains local definitions or structures.

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {x : ℝ} (hx : 0 ≤ x ∧ x < 1) (n : ℕ) : 1 - x^n ≠ 0 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_21_6b
  (f : ℕ → Icc 0 1 → ℝ)
  (h : ∀ x n, f n x = ↑x ^ n) :
  ¬ ∃ f₀, TendstoUniformly f f₀ atTop := by
  have hne := dummy_assumed (x := (0 : ℝ)) ⟨le_rfl, zero_lt_one⟩ 0
  simp at hne
