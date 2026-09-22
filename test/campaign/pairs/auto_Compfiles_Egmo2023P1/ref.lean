/-
Gold reference statement (verbatim from dwrensha/compfiles (Apache 2.0), extraction machinery stripped);
theorem renamed `Egmo2023P1_refs`, proof replaced by `sorry`.
-/
import Mathlib.Tactic

/-!
# European Girls' Mathematical Olympiad 2023, Problem 1

There are n ≥ 3 positive real numbers a_1, a_2, . . . , a_n. For each 1 ≤ i ≤ n we let
b_i = (a_(i-1) + a_(i+1)) / a_i (here we define a_0 to be a_n and a_(n+1) to be a_1).
Assume that for all i and j in the range 1 to n, we have a_i ≤ a_j if and only if b_i ≤ b_j.
Prove that a_1 = a_2 = ... = a_n.
-/

theorem Egmo2023P1_refs (n : ℕ) [NeZero n] (_ : n ≥ 3) (a : Fin n → ℝ) (ha : ∀ i, a i > 0)
    (b : Fin n → ℝ) (hb : ∀ i, b i = (a (i - 1) + a (i + 1)) / (a i))
    (h : ∀ i j, a i ≤ a j ↔ b i ≤ b j) : ∀ i j, a i = a j := by sorry
