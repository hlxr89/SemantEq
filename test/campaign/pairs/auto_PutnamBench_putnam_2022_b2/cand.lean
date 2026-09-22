/-
Autoformalized from NL only (blind); benchmark: PutnamBench; problem: putnam_2022_b2.
-/
import Mathlib

open Matrix

/-- The set of positive integers `n` for which such a set exists: `n = 1` (take `{0}`)
and `n = 7` (take `{0, ±e₁, ±e₂, ±e₃}`). -/
def putnam_2022_b2_solution : Set ℕ := {1, 7}

/-- Let $\times$ represent the cross product in $\mathbb{R}^3$. For what positive
integers $n$ does there exist a set $S \subset \mathbb{R}^3$ with exactly $n$ elements
such that $S=\{v \times w:v,w \in S\}$? -/
theorem putnam_2022_b2 (n : ℕ) (hn : 0 < n) :
    n ∈ putnam_2022_b2_solution ↔
      ∃ S : Set (Fin 3 → ℝ), S.Finite ∧ S.ncard = n ∧
        S = {u | ∃ v ∈ S, ∃ w ∈ S, u = v ⨯₃ w} := sorry
