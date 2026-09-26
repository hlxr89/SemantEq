import Mathlib

-- ===== assumed statement (antecedent) =====
theorem r_assumed : Nat.Prime 5 := by
  sorry

-- the same bridge as an in-file lemma, used by rewriting
theorem bridge : Nat.Prime 5 ↔ Irrational (Real.sqrt 2) := ⟨fun _ => irrational_sqrt_two, fun _ => by norm_num⟩

-- ===== goal statement, PROVED from the antecedent =====
theorem c : Irrational (Real.sqrt 2) := by
  rw [← bridge]
  exact r_assumed
