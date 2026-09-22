/-
Gold reference statement (verbatim from ProofNet#, Munkres.exercise_18_8a, Mathlib API migrated);
theorem renamed `exercise_18_8a_refs`, proof replaced by `sorry`.
-/
import Mathlib

open Filter Set TopologicalSpace
open scoped Topology
noncomputable section

/-- Let $Y$ be an ordered set in the order topology. Let $f, g: X \rightarrow Y$ be continuous. Show that the set $\{x \mid f(x) \leq g(x)\}$ is closed in $X$. -/
theorem exercise_18_8a_refs {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [LinearOrder Y] [OrderTopology Y] {f g : X → Y}
  (hf : Continuous f) (hg : Continuous g) :
  IsClosed {x | f x ≤ g x} :=
sorry
