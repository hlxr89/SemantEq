import Mathlib

-- ===== assumed statement (antecedent) =====
theorem c_assumed : Irrational (Real.sqrt 2) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem r : Nat.Prime 5 := by
  have h : Irrational (Real.sqrt 2) ↔ Nat.Prime 5 := ⟨fun _ => by norm_num, fun _ => irrational_sqrt_two⟩
  exact h.mp c_assumed
