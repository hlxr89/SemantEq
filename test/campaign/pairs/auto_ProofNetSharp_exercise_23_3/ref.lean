/-
Gold reference statement (verbatim from ProofNet#, Munkres.exercise_23_3, Mathlib API migrated);
theorem renamed `exercise_23_3_refs`, proof replaced by `sorry`.
-/
import Mathlib

open Filter Set TopologicalSpace
open scoped Topology
noncomputable section

/-- Let $\left\{A_{\alpha}\right\}$ be a collection of connected subspaces of $X$; let $A$ be a connected subset of $X$. Show that if $A \cap A_{\alpha} \neq \varnothing$ for all $\alpha$, then $A \cup\left(\bigcup A_{\alpha}\right)$ is connected. -/
theorem exercise_23_3_refs {X : Type*} [TopologicalSpace X]
  [TopologicalSpace X] {A : ℕ → Set X}
  (hAn : ∀ n, IsConnected (A n))
  (A₀ : Set X)
  (hA : IsConnected A₀)
  (h : ∀ n, A₀ ∩ A n ≠ ∅) :
  IsConnected (A₀ ∪ (⋃ n, A n)) :=
sorry
