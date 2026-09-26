import Mathlib

-- ===== assumed statement (antecedent) =====
theorem r_assumed : Nat.Prime 5 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
-- the same bridge as a propositional equation
theorem c : Irrational (Real.sqrt 2) := by
  have h : Nat.Prime 5 = Irrational (Real.sqrt 2) := propext ⟨fun _ => irrational_sqrt_two, fun _ => by norm_num⟩
  exact h ▸ r_assumed
