import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {p : ℕ} (hp : 1 ≤ p) : ¬ TendstoUniformly (fun n x => x ^ n) (fun x => 1) atTop := sorry
