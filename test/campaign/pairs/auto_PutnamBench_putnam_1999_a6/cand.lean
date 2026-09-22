/-
Autoformalized from NL only (blind); benchmark: PutnamBench; problem: putnam_1999_a6.
-/
import Mathlib

/-- The sequence $(a_n)_{n\geq 1}$ is defined by $a_1=1, a_2=2, a_3=24,$ and, for $n\geq 4$, \[a_n = \frac{6a_{n-1}^2a_{n-3} - 8a_{n-1}a_{n-2}^2}{a_{n-2}a_{n-3}}.\] Show that, for all n, $a_n$ is an integer multiple of $n$. -/
theorem putnam_1999_a6 (a : ℕ → ℚ)
    (ha1 : a 1 = 1) (ha2 : a 2 = 2) (ha3 : a 3 = 24)
    (ha : ∀ n : ℕ, 4 ≤ n →
      a n = (6 * (a (n - 1)) ^ 2 * a (n - 3) - 8 * a (n - 1) * (a (n - 2)) ^ 2) /
        (a (n - 2) * a (n - 3))) :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℤ, a n = (n : ℚ) * k := sorry
