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
theorem dummy {p : ℕ} (hp : 1 ≤ p) : ¬ TendstoUniformly (fun n x => x ^ n) (fun x => 1) atTop := by
  intro hu
  have hz := hu.tendsto_at 0
  have heq : (fun n : ℕ => (0 : ℕ) ^ n) =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp [Nat.ne_of_gt hn]
  have hzero : Tendsto (fun n : ℕ => (0 : ℕ) ^ n) atTop (𝓝 0) :=
    (tendsto_congr' heq).2 tendsto_const_nhds
  have : (1 : ℕ) = 0 := tendsto_nhds_unique hz hzero
  omega
