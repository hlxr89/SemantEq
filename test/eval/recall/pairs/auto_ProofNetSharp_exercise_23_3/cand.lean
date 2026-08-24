/-
Autoformalized from NL only (blind); benchmark: ProofNetSharp; problem: exercise_23_3.
-/
import Mathlib

/-- Let $\left\{A_{\alpha}\right\}$ be a collection of connected subspaces of $X$; let $A$ be a
connected subset of $X$. Show that if $A \cap A_{\alpha} \neq \varnothing$ for all $\alpha$, then
$A \cup\left(\bigcup A_{\alpha}\right)$ is connected. -/
theorem exercise_23_3 {X : Type*} [TopologicalSpace X] {ι : Type*}
    (A : Set X) (Aa : ι → Set X)
    (hA : IsConnected A) (hAa : ∀ α, IsConnected (Aa α))
    (hmeet : ∀ α, (A ∩ Aa α).Nonempty) :
    IsConnected (A ∪ ⋃ α, Aa α) := sorry
