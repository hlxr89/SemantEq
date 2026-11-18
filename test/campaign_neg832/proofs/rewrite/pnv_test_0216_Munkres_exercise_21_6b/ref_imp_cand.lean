import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- The unified context is empty.

-- ===== assumed statement (antecedent) =====
theorem exercise_21_6b_assumed
  (f : ℕ → Icc 0 1 → ℝ)
  (h : ∀ x n, f n x = ↑x ^ n) :
  ¬ ∃ f₀, TendstoUniformly f f₀ atTop := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {n : ℕ} : ¬ TendstoUniformlyOn (fun (n : ℕ) (x : ℝ) => x ^ n) (fun x => x) atTop (Set.Icc 0 1) := by
  intro h_uniform
  apply exercise_21_6b_assumed
    (fun (n : ℕ) (x : Icc (0 : ℕ) 1) => (x : ℝ) ^ n)
    (by
      intro x n
      rfl)
  refine ⟨fun x => (x : ℝ), ?_⟩
  intro u hu
  filter_upwards [h_uniform u hu] with n hn
  intro x
  exact hn (x : ℝ) ⟨Nat.cast_nonneg x, by exact_mod_cast x.property.2⟩
