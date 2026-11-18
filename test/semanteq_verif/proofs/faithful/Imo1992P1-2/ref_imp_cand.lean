import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev solution_set : Set (ℤ × ℤ × ℤ) := {(2, 4, 8), (3, 5, 15)}

-- ===== assumed statement (antecedent) =====
theorem imo1992_p1_assumed (a b c : ℤ) (ha : 1 < a) (hb : a < b) (hc : b < c) :
    ⟨a, b, c⟩ ∈ solution_set ↔
    (a - 1) * (b - 1) * (c - 1) ∣ a * b * c - 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement : 
  ∀ a b c : ℤ, (1 < a ∧ a < b ∧ b < c ∧ (a - 1) * (b - 1) * (c - 1) ∣ a * b * c - 1) ↔
  ((a = 2 ∧ b = 4 ∧ c = 8) ∨ (a = 3 ∧ b = 5 ∧ c = 15)) := by
  intro a b c
  constructor
  · rintro ⟨ha, hb, hc, hdvd⟩
    have hmem := (imo1992_p1_assumed a b c ha hb hc).2 hdvd
    simpa [solution_set] using hmem
  · intro hsol
    have hmem : ⟨a, b, c⟩ ∈ solution_set := by
      simpa [solution_set] using hsol
    rcases hsol with hsol | hsol
    · rcases hsol with ⟨rfl, rfl, rfl⟩
      refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
      exact (imo1992_p1_assumed 2 4 8 (by norm_num) (by norm_num) (by norm_num)).1 hmem
    · rcases hsol with ⟨rfl, rfl, rfl⟩
      refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
      exact (imo1992_p1_assumed 3 5 15 (by norm_num) (by norm_num) (by norm_num)).1 hmem
