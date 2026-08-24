/-
Autoformalized from NL only (blind); benchmark: Compfiles; problem: Egmo2023P1.
-/
import Mathlib

/-- There are n ≥ 3 positive real numbers a_1, a_2, . . . , a_n. For each 1 ≤ i ≤ n we let
b_i = (a_(i-1) + a_(i+1)) / a_i (here we define a_0 to be a_n and a_(n+1) to be a_1).
Assume that for all i and j in the range 1 to n, we have a_i ≤ a_j if and only if b_i ≤ b_j.
Prove that a_1 = a_2 = ... = a_n.

The cyclic indexing is modeled with `ZMod n`. -/
theorem Egmo2023P1 (n : ℕ) (hn : 3 ≤ n) (a b : ZMod n → ℝ)
    (ha : ∀ i, 0 < a i)
    (hb : ∀ i, b i = (a (i - 1) + a (i + 1)) / a i)
    (hab : ∀ i j, a i ≤ a j ↔ b i ≤ b j) :
    ∀ i j, a i = a j :=
  sorry
