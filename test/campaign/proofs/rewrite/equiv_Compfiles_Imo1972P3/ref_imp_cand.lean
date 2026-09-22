import Mathlib

open scoped Nat

namespace Imo1972P3

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem imo1972_p3_assumed (m n : ℕ) :
    m ! * n ! * (m + n)! ∣ (2 * m)! * (2 * n)! := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1972_p3_alt (m n : ℕ) :
    ∃ k, (2 * m)! * (2 * n)! = m ! * n ! * (m + n)! * k := by
  exact imo1972_p3_assumed m n

end Imo1972P3
