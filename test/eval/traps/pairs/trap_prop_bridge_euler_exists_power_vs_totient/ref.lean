import Mathlib
theorem r (a n : ℕ) (hn : 0 < n) (hcop : Nat.Coprime a n) : ∃ k, 0 < k ∧ a ^ k ≡ 1 [MOD n] := by sorry