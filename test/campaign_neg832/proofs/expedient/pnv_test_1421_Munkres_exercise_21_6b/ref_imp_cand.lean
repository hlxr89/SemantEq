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
  have he := hu SetRel.id (DiscreteUniformity.relId_mem_uniformity ℕ)
  rcases (he.and (eventually_ge_atTop 1)).exists with ⟨n, hn, hn1⟩
  have hz := hn 0
  simp [SetRel.id, Nat.zero_pow (by omega : 0 < n)] at hz
