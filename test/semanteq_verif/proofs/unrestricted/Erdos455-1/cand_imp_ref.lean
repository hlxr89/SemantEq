import Mathlib

open Filter ENNReal

namespace Erdos455

-- ===== unified context (both sides' local defs, merged) =====
-- empty

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
  intro q hq hgap
  apply erdos_455_assumed q hq
  intro n
  constructor
  · exact (hgap n).1
  · cases n with
    | zero => simp
    | succ n =>
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using (hgap n).2

end Erdos455
