import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {a b : ℕ → ℝ} (ha : Tendsto (fun n => a n) atTop atTop) (hb : Tendsto (fun n => b n) atTop atTop) : Tendsto (fun n => a n + b n) atTop atTop ∧ limsup (fun n => a n + b n) ≤ limsup (fun n => a n) + limsup (fun n => b n) := sorry
