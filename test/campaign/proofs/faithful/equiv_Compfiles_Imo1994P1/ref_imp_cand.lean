import Mathlib
open Finset

-- ===== unified context (both sides' local defs, merged) =====
-- empty

namespace Imo1994P1

-- ===== assumed statement (antecedent) =====
theorem imo1994_p1_assumed (n : ℕ) (m : ℕ) (A : Finset ℕ) (hm : A.card = m + 1)
    (hrange : ∀ a ∈ A, 0 < a ∧ a ≤ n)
    (hadd : ∀ a ∈ A, ∀ b ∈ A, a + b ≤ n → a + b ∈ A) :
    (m + 1) * (n + 1) ≤ 2 * ∑ x ∈ A, x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1994_p1_alt (n : ℕ) (m : ℕ) (A : Finset ℕ) (hm : A.card = m + 1)
    (hrange : ∀ a ∈ A, 1 ≤ a ∧ a ≤ n)
    (hadd : ∀ a ∈ A, ∀ b ∈ A, a + b ≤ n → a + b ∈ A) :
    2 * ∑ x ∈ A, x ≥ (m + 1) * (n + 1) := by
  apply imo1994_p1_assumed n m A hm
  · intro a ha
    exact ⟨(Nat.succ_le_iff).mp (hrange a ha).1, (hrange a ha).2⟩
  · exact hadd

end Imo1994P1
