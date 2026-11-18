import Mathlib

open Filter Real Function
open scoped Topology

theorem dummy {p : ℝ} (hp : 1 < p) : Summable fun n => 1 / n * (log n : ℝ) ^ p := sorry
