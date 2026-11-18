import Mathlib

open Filter Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

namespace Erdos15

-- ===== assumed statement (antecedent) =====
theorem erdos_15_assumed : 
    Summable (fun k : ℕ => (-1 : ℚ) ^ (k + 1) * (k + 1) / (k.nth Nat.Prime)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_15_goal :
    ∃ l : ℝ, Tendsto (fun N => ∑ k ∈ Finset.range N,
      (-1 : ℝ) ^ (k + 1) * (k + 1) / (k.nth Nat.Prime)) atTop (𝓝 l) := by
  let f : ℕ → ℚ := fun k => (-1 : ℚ) ^ (k + 1) * (k + 1) / (k.nth Nat.Prime)
  have hf : Summable f := erdos_15_assumed
  have hcast : HasSum (fun k => (f k : ℝ)) ((∑' k, f k : ℚ) : ℝ) := by
    simpa [Function.comp_def] using
      hf.hasSum.map (Rat.castHom ℝ) Rat.continuous_coe_real
  refine ⟨((∑' k, f k : ℚ) : ℝ), ?_⟩
  simpa [f] using hcast.tendsto_sum_nat

end Erdos15
