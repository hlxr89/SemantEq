/-
Autoformalized from NL only (blind); benchmark: PutnamBench; problem: putnam_1971_a1.
-/
import Mathlib

/-- Let $S$ be a set of $9$ lattice points (points with integer coordinates) in
$3$-dimensional Euclidean space. Prove that there exists a lattice point along the
interior of some line segment that joins two distinct points in $S$. -/
theorem putnam_1971_a1 (S : Finset (Fin 3 → ℤ)) (hS : S.card = 9) :
    ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ ∃ z : Fin 3 → ℤ,
      (fun i => (z i : ℝ)) ∈
        openSegment ℝ (fun i => (p i : ℝ)) (fun i => (q i : ℝ)) := sorry
