import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {f g : ℕ → ℝ} : limsup (fun n => f n + g n) ≤ limsup f + limsup g := sorry
