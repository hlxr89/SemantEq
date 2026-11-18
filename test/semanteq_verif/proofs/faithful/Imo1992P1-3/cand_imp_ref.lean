import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev solution_set : Set (ℤ × ℤ × ℤ) := {(2, 4, 8), (3, 5, 15)}

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  ∀ a b c : ℤ, 1 < a ∧ a < b ∧ b < c ∧ (a - 1) * (b - 1) * (c - 1) ∣ a * b * c - 1 →
    (a = 2 ∧ b = 4 ∧ c = 8) ∨ (a = 3 ∧ b = 5 ∧ c = 15) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1992_p1 (a b c : ℤ) (ha : 1 < a) (hb : a < b) (hc : b < c) :
    ⟨a, b, c⟩ ∈ solution_set ↔
    (a - 1) * (b - 1) * (c - 1) ∣ a * b * c - 1 := by
  constructor
  · intro hmem
    simp only [solution_set, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h
    · rcases h with ⟨rfl, rfl, rfl⟩
      norm_num
    · rcases h with ⟨rfl, rfl, rfl⟩
      norm_num
  · intro hdiv
    have hsol := problem_statement_assumed a b c ⟨ha, hb, hc, hdiv⟩
    simpa [solution_set] using hsol
