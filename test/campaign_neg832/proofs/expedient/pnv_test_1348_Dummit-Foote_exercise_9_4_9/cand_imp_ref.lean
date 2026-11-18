import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type*} [CommRing R] [IsDomain R] [Algebra ℤ R] (hR : ∀ a b : R, Irreducible (a * b) → Irreducible a ∨ Irreducible b) (hsqrt2 : IsIntegral ℤ (sqrt2 : R)) : Irreducible (Polynomial.map (algebraMap ℤ R) (Polynomial.X^2 - C (sqrt2))) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_4_9 :
  Irreducible (X^2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) := by
  change Irreducible (X^2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd (2 : ℕ)))
  letI dnsq : Zsqrtd.Nonsquare 2 := ⟨by
    intro n h
    have hn : n < 2 := by
      by_contra hn
      have : 4 ≤ n * n := Nat.mul_le_mul (show 2 ≤ n by omega) (show 2 ≤ n by omega)
      omega
    interval_cases n <;> omega⟩
  letI : NoZeroDivisors (Zsqrtd 2) :=
    { eq_zero_or_eq_zero_of_mul_eq_zero := @Zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero 2 dnsq }
  letI : IsDomain (Zsqrtd 2) := NoZeroDivisors.to_isDomain _
  apply ((monic_X_pow_sub_C Zsqrtd.sqrtd (by decide)).irreducible_iff_roots_eq_zero_of_degree_le_three
    (by simp) (by simp)).2
  apply Multiset.eq_zero_of_forall_notMem
  rintro ⟨a, b⟩ h
  have hr : IsRoot (X^2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd (2 : ℕ))) ⟨a, b⟩ :=
    (mem_roots (by
      intro hp
      have hc := congr_arg (coeff · 2) hp
      simp at hc)).1 h
  simp [IsRoot, Zsqrtd.ext_iff, pow_two] at hr
  rcases hr with ⟨hr, hi⟩
  change a * a + 2 * b * b = 0 at hr
  have hi' : 2 * a * b - 1 = 0 := by nlinarith [hi]
  nlinarith [sq_nonneg a, sq_nonneg b]
