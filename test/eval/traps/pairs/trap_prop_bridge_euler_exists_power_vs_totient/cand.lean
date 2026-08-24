import Mathlib
theorem c (a n : ℕ) (hn : 0 < n) (hcop : Nat.Coprime a n) : a ^ Nat.totient n ≡ 1 [MOD n] := by sorry