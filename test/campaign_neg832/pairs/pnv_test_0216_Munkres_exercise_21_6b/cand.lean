import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {n : ℕ} : ¬ TendstoUniformlyOn (fun (n : ℕ) (x : ℝ) => x ^ n) (fun x => x) atTop (Set.Icc 0 1) := sorry
