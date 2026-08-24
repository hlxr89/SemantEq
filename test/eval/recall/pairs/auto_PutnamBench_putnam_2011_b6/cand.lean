/-
Autoformalized from NL only (blind); benchmark: PutnamBench; problem: putnam_2011_b6.
-/
import Mathlib

open Nat

/-- Let $p$ be an odd prime. Show that for at least $(p+1)/2$ values of $n$ in
$\{0,1,2,\dots,p-1\}$,
\[
\sum_{k=0}^{p-1} k! n^k \qquad \mbox{is not divisible by $p$.}
\] -/
theorem putnam_2011_b6 (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    (p + 1) / 2 ≤
      ((Finset.range p).filter
        (fun n => ¬ p ∣ ∑ k ∈ Finset.range p, k ! * n ^ k)).card := sorry
