import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev PosInt : Type := { x : ℤ // 0 < x }

notation "ℤ>0" => PosInt

abbrev SolutionSet : Set (ℤ>0 → ℤ>0) := { f | f = id ∨ ∃ c, ∀ x, f x = x + c }

-- ===== assumed statement (antecedent) =====
theorem imo2010_p3_assumed (g : ℤ>0 → ℤ>0) :
    g ∈ SolutionSet ↔ ∀ m n, IsSquare ((g m + n) * (g n + m)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement :
  ∀ g : ℕ → ℕ,
    (∀ n : ℕ, g n > 0) →
    (∀ m n : ℕ, m > 0 → n > 0 → ∃ k : ℕ, (g m + n) * (g n + m) = k^2) ↔ 
    ∃ c : ℕ, ∀ n : ℕ, n > 0 → g n = n + c := by
  -- not proved: as parsed, the left side is vacuously true when g 0 = 0, regardless of g on positive inputs.
  sorry
