import Mathlib

open Filter ENNReal

-- ===== unified context (both sides' local defs, merged) =====
-- The unified context is empty.

namespace Erdos455

-- ===== assumed statement (antecedent) =====
theorem erdos_455_assumed :
    ∀ q : ℕ → ℕ, StrictMono q →
    (∀ n, (q n).Prime ∧ q (n + 1) - q n ≥ q n - q (n - 1)) →
    Tendsto (fun n : ℕ => (q n : ℝ) / n ^ 2) atTop atTop := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_455_goal :
    ∀ q : ℕ → ℕ, StrictMono q →
    (∀ n, (q n).Prime ∧ q (n + 2) - q (n + 1) ≥ q (n + 1) - q n) →
    Tendsto (fun n : ℕ => (q n : ℝ) / n ^ 2) atTop atTop := by
  intro q hq h
  apply erdos_455_assumed q hq
  intro n
  constructor
  · exact (h n).1
  · cases n with
    | zero =>
        simpa only [Nat.zero_sub, Nat.sub_self] using
          (Nat.zero_le (q (0 + 1) - q 0))
    | succ n => simpa only [Nat.add_sub_cancel] using (h n).2

end Erdos455
