import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed : Irreducible (Polynomial.C (1 : ℤ) + Polynomial.X + 6 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 + Polynomial.X ^ 4) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_4_2c : Irreducible
  (X^4 + 4*X^3 + 6*X^2 + 2*X + 1 : Polynomial ℤ) := by
  let f : Polynomial ℤ := X^4 + 4*X^3 + 6*X^2 + 2*X + 1
  let g : Polynomial ℤ := X^4 - 2*X + 2
  have hgimd : IsMonicOfDegree g 4 := by
    dsimp [g]
    rw [show X^4 - 2*X + 2 = X^4 + (-2*X + 2) by ring]
    apply (isMonicOfDegree_X_pow ℤ 4).add_right
    compute_degree <;> norm_num
  have hgmonic : g.Monic := hgimd.monic
  have hgdeg : g.degree = 4 := by
    rw [degree_eq_natDegree hgmonic.ne_zero, hgimd.natDegree_eq]
    norm_num
  have hg : Irreducible g := by
    apply irreducible_of_eisenstein_criterion (P := Ideal.span {(2 : ℤ)})
    · rw [Ideal.span_singleton_prime (by norm_num), Int.prime_iff_natAbs_prime]
      exact Nat.prime_two
    · rw [hgmonic.leadingCoeff, Ideal.mem_span_singleton]
      norm_num
    · intro n hn
      rw [hgdeg] at hn
      norm_cast at hn
      interval_cases n <;> simp [g, Ideal.mem_span_singleton]
    · rw [hgdeg]
      norm_num
    · rw [show g.coeff 0 = 2 by simp [g], Ideal.span_singleton_pow,
          Ideal.mem_span_singleton]
      norm_num
    · exact hgmonic.isPrimitive
  have hcomp : f.comp (X + C (-1)) = g := by
    dsimp [f, g]
    simp only [add_comp, mul_comp, X_pow_comp, X_comp, natCast_comp, ofNat_comp, one_comp]
    norm_num
    ring
  let e := Polynomial.algEquivAevalXAddC (-1 : ℤ)
  apply (MulEquiv.irreducible_iff e.toRingEquiv.toMulEquiv).mp
  have he : e f = g := by
    simpa [e, ← comp_eq_aeval] using hcomp
  change Irreducible (e f)
  rw [he]
  exact hg
