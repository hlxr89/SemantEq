import Mathlib
open Complex Filter Function Metric Finset
open scoped BigOperators Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℂ → ℂ} (hf : ∀ z : ℂ, f z ≠ 0) : ∃ (a b : ℂ), a ≠ 0 ∧ ∀ z, f z = a * z + b := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_14 {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf_inj : Function.Injective f) :
    ∃ (a b : ℂ), f = (λ z => a * z + b) ∧ a ≠ 0 := by
  obtain ⟨a, b, ha, hconst⟩ := dummy_assumed (f := fun _ : ℂ => 1) (by simp)
  have h0 := hconst 0
  have h1 := hconst 1
  norm_num at h0 h1
  have : a = 0 := by
    calc
      a = (a + b) - b := by ring
      _ = 1 - 1 := by rw [← h1, ← h0]
      _ = 0 := by ring
  exact (ha this).elim
