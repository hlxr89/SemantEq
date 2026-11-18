import Mathlib

open Asymptotics Filter Finset

namespace Erdos289

-- ===== unified context (both sides' local defs, merged) =====
-- Empty: neither preamble has local definitions or structures.

-- ===== assumed statement (antecedent) =====
theorem erdos_289_assumed : 
    (∀ᶠ k : ℕ in atTop, ∃ I : Fin k → ℕ × ℕ,
    (∀ i, (I i).1 < (I i).2) ∧
    (∀ i j, i ≠ j → (I i).2 < (I j).1 ∨ (I j).2 < (I i).1) ∧
    ∑ i, ∑ n ∈ .Icc (I i).1 (I i).2, (n⁻¹ : ℚ) = 1) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_289 :
    (∀ᶠ k : ℕ in atTop, ∃ I : Fin k → ℕ × ℕ,
    (∀ i, (I i).1 < (I i).2) ∧
    (∀ i j, i ≠ j → (I i).2 + 1 < (I j).1 ∨ (I j).2 + 1 < (I i).1) ∧
    ∑ i, ∑ n ∈ .Icc (I i).1 (I i).2, (n⁻¹ : ℚ) = 1) := by
  -- not proved: the candidate permits adjacent inclusive intervals, while the reference requires a strict one-integer gap.
  sorry

end Erdos289
