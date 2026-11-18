import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type*} [CommRing R] [IsDomain R] [GCDMonoid R] [IsPrincipalIdealRing R] [IsDedekindDomain R] (n : ℕ) (hn : Nat.Prime n) (hn1 : n ≠ 1) (hn3 : 3 < n) : Irreducible (n : R) ∧ Irreducible (1 + (n : R)) ∧ Irreducible ((n : R) * (1 - (n : R))) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_8_3_5a {n : ℤ} (hn0 : n > 3) (hn1 : Squarefree n) :
  Irreducible (2 : Zsqrtd $ -n) ∧
  Irreducible (⟨0, 1⟩ : Zsqrtd $ -n) ∧
  Irreducible (1 + ⟨0, 1⟩ : Zsqrtd $ -n) := by
  -- not proved: the candidate statement supplies irreducibility only for unrelated natural-number casts and their expressions
  sorry
