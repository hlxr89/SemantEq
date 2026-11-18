import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type*} [CommRing R] [IsDomain R] {a : R} (ha2 : a ^ 2 = 2) : Irreducible (X^2 - C a) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_4_9 :
  Irreducible (X^2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) := by
  letI : Zsqrtd.Nonsquare 2 := ⟨by
    intro n hn
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp ⟨n, hn⟩ with h | h
    · subst n
      norm_num at hn
    · subst n
      norm_num at hn⟩
  letI : IsDomain (Zsqrtd (2 : ℤ)) := @Zsqrtd.instIsDomainCastInt 2 inferInstance
  change Irreducible (X^2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd (2 : ℕ)))
  apply dummy_assumed
  simpa [pow_two] using (Zsqrtd.dmuld (d := 2))
