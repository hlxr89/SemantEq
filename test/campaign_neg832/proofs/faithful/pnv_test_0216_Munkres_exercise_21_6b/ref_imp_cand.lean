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
theorem dummy {n : ℕ} : ¬ TendstoUniformlyOn (fun (n : ℕ) (x : ℝ) => x ^ n) (fun x => x) atTop (Set.Icc 0 1) := by
  -- not proved: ref's Icc is inferred over ℕ, while cand's interval is over ℝ; only vacuity could prove this direction
  sorry
