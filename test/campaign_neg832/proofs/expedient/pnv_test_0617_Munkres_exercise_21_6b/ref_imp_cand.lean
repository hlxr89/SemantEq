import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_21_6b_assumed
  (f : ℕ → Icc 0 1 → ℝ)
  (h : ∀ x n, f n x = ↑x ^ n) :
  ¬ ∃ f₀, TendstoUniformly f f₀ atTop := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy : ¬UniformContinuous (fun x : ℝ => x ^ (n : ℕ)) := by
  intro _
  apply exercise_21_6b_assumed (fun m x => (x : ℝ) ^ m) (by simp)
  refine ⟨fun x => (x : ℝ), ?_⟩
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [eventually_ge_atTop 1] with m hm x
  have hx : (x : ℕ) = 0 ∨ (x : ℕ) = 1 := by
    rcases x.property with ⟨hx0, hx1⟩
    omega
  rcases hx with hx | hx <;> simp [hx, Nat.ne_of_gt hm, hε]
