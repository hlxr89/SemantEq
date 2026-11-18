import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

namespace Erdos488

-- ===== assumed statement (antecedent) =====
theorem erdos_488_assumed :
    ∀ (A : Finset ℕ), A.Nonempty →
    0 ∉ A → 1 ∉ A →
    letI B := {n ≥ 1 | ∃ a ∈ A, a ∣ n}
    ∀ᵉ (n : ℕ) (m > n), A.max ≤ n →
      ((Finset.Icc 1 m).filter (· ∈ B)).card / (m : ℚ) <
        2 * ((Finset.Icc 1 n).filter (· ∈ B)).card / n := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_488 :
    ∀ (A : Finset ℕ), A.Nonempty →
    letI B := {n ≥ 1 | ∃ a ∈ A, a ∣ n}
    ∀ᵉ (n : ℕ) (m > n), A.max ≤ n →
      ((Finset.Icc 1 m).filter (· ∈ B)).card / (m : ℚ) <
        2 * ((Finset.Icc 1 n).filter (· ∈ B)).card / n := by
  -- not proved: false for A = {0}, when the required strict inequality is 0 < 0
  sorry

end Erdos488
