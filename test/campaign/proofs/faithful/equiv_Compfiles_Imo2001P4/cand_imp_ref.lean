import Mathlib

namespace Imo2001Q4

open Equiv Finset
open scoped Nat

-- ===== unified context (both sides' local defs, merged) =====
variable {n : ℕ} {c : Fin n → ℤ}

/-- The function `S` in the problem. As implemented here it accepts a
permutation of `Fin n` rather than `Icc 1 n`, and as such contains `+ 1`
to compensate. -/
def S (c : Fin n → ℤ) (a : Perm (Fin n)) : ℤ := ∑ i, c i * (a i + 1)

-- ===== assumed statement (antecedent) =====
theorem imo2001_p4_alt_assumed (hodd : Odd n) (hlt : 1 < n) :
    ∃ a b, a ≠ b ∧ (n ! : ℤ) ∣ S c a - S c b := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2001_p4 (hn : Odd n ∧ 1 < n) :
    ∃ a b, a ≠ b ∧ (n ! : ℤ) ∣ S c a - S c b := by
  exact imo2001_p4_alt_assumed hn.1 hn.2

end Imo2001Q4
