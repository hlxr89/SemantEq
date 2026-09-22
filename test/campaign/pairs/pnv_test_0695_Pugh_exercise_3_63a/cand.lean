import Mathlib

open Filter Real Function
open scoped Topology

theorem dummy (p : ℝ) (hp : 1 < p) : Summable fun k => 1 / (k * (log k)^p) := sorry
