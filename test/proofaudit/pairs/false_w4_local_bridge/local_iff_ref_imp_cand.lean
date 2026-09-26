import Mathlib

-- ===== assumed statement (antecedent) =====
theorem r_assumed : Nat.Prime 5 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
-- Two unrelated library-true statements, joined by a local iff whose two
-- directions ignore their hypothesis. Must FAIL: the direction used proves
-- the goal from the library alone.
theorem c : Irrational (Real.sqrt 2) := by
  have h : Nat.Prime 5 ↔ Irrational (Real.sqrt 2) := ⟨fun _ => irrational_sqrt_two, fun _ => by norm_num⟩
  exact h.mp r_assumed
