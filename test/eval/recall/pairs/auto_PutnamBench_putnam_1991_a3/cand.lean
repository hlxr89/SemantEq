/-
Autoformalized from NL only (blind); benchmark: PutnamBench; problem: putnam_1991_a3.
-/
import Mathlib

open Polynomial

/-- The polynomials satisfying the condition: exactly the quadratics with two distinct real roots. -/
def putnam_1991_a3_solution : Set (Polynomial ℝ) :=
  {p | ∃ c a b : ℝ, c ≠ 0 ∧ a < b ∧ p = C c * (X - C a) * (X - C b)}

/-- Find all real polynomials $p(x)$ of degree $n \geq 2$ for which there exist real numbers $r_1< r_2<\cdots< r_n$ such that
\begin{enumerate}
\item $p(r_i)=0, \qquad i=1,2,\dots,n$, and
\item $p'(\frac{r_i+r_{i+1}}{2})=0 \qquad i=1,2,\dots,n-1$,
\end{enumerate}
where $p'(x)$ denotes the derivative of $p(x)$. -/
theorem putnam_1991_a3 (n : ℕ) (hn : 2 ≤ n) (p : Polynomial ℝ) (hdeg : p.natDegree = n) :
    (∃ r : ℕ → ℝ,
      (∀ i ∈ Finset.Icc 1 n, ∀ j ∈ Finset.Icc 1 n, i < j → r i < r j) ∧
      (∀ i ∈ Finset.Icc 1 n, p.eval (r i) = 0) ∧
      (∀ i ∈ Finset.Icc 1 (n - 1), (derivative p).eval ((r i + r (i + 1)) / 2) = 0)) ↔
    p ∈ putnam_1991_a3_solution := sorry
