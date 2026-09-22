/-
Autoformalized from NL only (blind); benchmark: PutnamBench; problem: putnam_2008_b4.
-/
import Mathlib

/-- Let $p$ be a prime number. Let $h(x)$ be a polynomial with integer coefficients such that $h(0), h(1), \dots, h(p^2-1)$ are distinct modulo $p^2$. Show that $h(0), h(1), \dots, h(p^3-1)$ are distinct modulo $p^3$. -/
theorem putnam_2008_b4 (p : ℕ) (hp : p.Prime) (h : Polynomial ℤ)
    (hh : ∀ i j : ℕ, i < p ^ 2 → j < p ^ 2 →
      h.eval (i : ℤ) ≡ h.eval (j : ℤ) [ZMOD (p : ℤ) ^ 2] → i = j) :
    ∀ i j : ℕ, i < p ^ 3 → j < p ^ 3 →
      h.eval (i : ℤ) ≡ h.eval (j : ℤ) [ZMOD (p : ℤ) ^ 3] → i = j := sorry
