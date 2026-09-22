import Mathlib

namespace Usa2019P1

-- ===== unified context (both sides' local defs, merged) =====
def solution_set : Set ℕ+ := { x : ℕ+ | Even x.val }

-- ===== assumed statement (antecedent) =====
theorem usa2019_p1_alt_assumed (m : ℕ+) :
    (∃ f : ℕ+ → ℕ+,
      (∀ n, f^[f n] n * f (f n) = n * n) ∧
      m = f 1000) ↔ m ∈ solution_set := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem usa2019_p1 (m : ℕ+) :
   m ∈ solution_set ↔
    (∃ f : ℕ+ → ℕ+,
      (∀ n, f^[f n] n * f (f n) = n ^ 2) ∧
      m = f 1000) := by
  simpa [pow_two] using (usa2019_p1_alt_assumed m).symm

end Usa2019P1
