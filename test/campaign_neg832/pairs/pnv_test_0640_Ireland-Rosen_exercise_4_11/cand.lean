import Mathlib

open Real
open scoped BigOperators

theorem dummy {p : ℕ} [Fact p.Prime] {k : ℕ} (h : k % (p - 1) = 0) : ((Finset.range (p - 1)).sum fun i => (Nat.fib (i + 1)) ^ k) ≡ 0 [MOD p] := sorry
