/-
Autoformalized from NL only (blind); benchmark: PutnamBench; problem: putnam_1965_b3.
-/
import Mathlib

/-- Prove that there are exactly three right triangles (up to orientation and translation) with integer side lengths and area equal to twice their perimeter. -/
theorem putnam_1965_b3 :
    {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ t.1 ≤ t.2.1 ∧ t.1 ^ 2 + t.2.1 ^ 2 = t.2.2 ^ 2 ∧
      t.1 * t.2.1 = 4 * (t.1 + t.2.1 + t.2.2)}.ncard = 3 := sorry
