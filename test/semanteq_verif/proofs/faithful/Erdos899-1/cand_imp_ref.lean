import Mathlib

open Filter Set

open scoped Pointwise Topology

namespace Erdos899

open Erdos899

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem erdos_899_assumed : ∀ (A : Set ℕ), A.Infinite →
    Tendsto (fun N => (A ∩ Icc 1 N |>.ncard : ℝ) / N) atTop (𝓝 0) →
    Tendsto (fun N => ((A - A : Set ℕ) ∩ Icc 1 N |>.ncard : ℝ) /
      (A ∩ Icc 1 N).ncard) atTop atTop := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_899 : ∀ (A : Set ℕ), A.Infinite →
    Tendsto (fun N => (A ∩ Icc 1 N |>.ncard : ℝ) / N) atTop (𝓝 0) →
    atTop.limsup (fun N => ((A - A : Set ℕ) ∩ Icc 1 N |>.ncard : EReal) /
      (A ∩ Icc 1 N).ncard) = ⊤ := by
  intro A hA hzero
  have h := erdos_899_assumed A hA hzero
  have h' : Tendsto
      (fun N => (((((A - A : Set ℕ) ∩ Icc 1 N).ncard : ℝ) /
        (A ∩ Icc 1 N).ncard : ℝ) : EReal)) atTop (𝓝 ⊤) :=
    EReal.tendsto_coe_nhds_top_iff.2 h
  simpa using h'.limsup_eq

end Erdos899
