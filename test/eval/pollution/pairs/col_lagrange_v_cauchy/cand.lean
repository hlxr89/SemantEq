import Mathlib
theorem c (G : Type) [Group G] [Fintype G] (p : ℕ) [Fact (Nat.Prime p)] (hdvd : p ∣ Fintype.card G) : ∃ x : G, orderOf x = p := by sorry