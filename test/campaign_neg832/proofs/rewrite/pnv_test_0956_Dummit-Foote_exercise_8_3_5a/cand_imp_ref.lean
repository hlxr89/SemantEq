import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (n : ℕ) [Fact (1 < n)] [Fact (Nat.Prime n)] (h3 : n % 4 = 3) : Irreducible (2 : Polynomial (Zsqrtd (-n))) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_8_3_5a {n : ℤ} (hn0 : n > 3) (hn1 : Squarefree n) :
  Irreducible (2 : Zsqrtd $ -n) ∧
  Irreducible (⟨0, 1⟩ : Zsqrtd $ -n) ∧
  Irreducible (1 + ⟨0, 1⟩ : Zsqrtd $ -n) := by
  -- not proved: the antecedent only covers natural primes congruent to 3 modulo 4 and supplies no transport for the other two irreducibility conclusions
  sorry
