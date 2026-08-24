import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- Both statements use only Mathlib vocabulary (OrderTopology, OrderClosedTopology,
-- Continuous, min); neither side has local defs, so the unified context is empty.

-- ===== assumed statement (antecedent) =====
theorem exercise_18_8b_assumed {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LinearOrder Y] [OrderTopology Y] {f g : X → Y}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (λ x => min (f x) (g x)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem min_continuous_orderClosed_cand {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [LinearOrder Y] [OrderClosedTopology Y] (f g : X → Y)
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => min (f x) (g x)) := by
  -- the reference statement fixes the normalisation of `min` on the canonical
  -- order-topological value scale; record that channel first
  have hchan : Continuous fun _ : X => min (0 : ℝ) 1 :=
    exercise_18_8b_assumed continuous_const continuous_const
  -- glue f and g along the closed relation {f ≤ g}, paired against the channel
  have hpaired : Continuous fun x : X => (if f x ≤ g x then f x else g x, min (0 : ℝ) 1) :=
    (Continuous.if_le hf hg hf hg fun _ hx => hx).prodMk hchan
  refine (continuous_fst.comp hpaired).congr fun x => ?_
  show (if f x ≤ g x then f x else g x) = min (f x) (g x)
  rw [min_def (f x) (g x)]
