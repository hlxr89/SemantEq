import Mathlib

open Filter Real Function
open scoped Topology

theorem dummy {p : ℝ} (hp : 1 < p) : Tendsto (fun (k : ℕ) => 1/(k * (log k)^p) : ℕ → ℝ) atTop (𝓝 0) := sorry
