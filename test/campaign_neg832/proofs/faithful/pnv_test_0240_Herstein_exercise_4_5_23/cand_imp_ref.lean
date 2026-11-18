import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (F : Type*) [Field F] [Fintype F] (p q : F[X]) (hF : Fintype.card F = 7) (hp : p = X ^ 3 - 2) (hq : q = X ^ 3 + 2) (hp_irred : Irreducible p) (hq_irred : Irreducible q) : Nonempty (F[X] ⧸ Ideal.span {p} ≃+* F[X] ⧸ Ideal.span {q}) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_5_23 {p q: Polynomial (ZMod 7)}
  (hp : p = X^3 - 2) (hq : q = X^3 + 2) :
  Irreducible p ∧ Irreducible q ∧
  (Nonempty $ Polynomial (ZMod 7) ⧸ span ({p} : Set $ Polynomial $ ZMod 7) ≃+*
  Polynomial (ZMod 7) ⧸ span ({q} : Set $ Polynomial $ ZMod 7)) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hminus : ∀ x : ZMod 7, x ^ 3 - 2 ≠ 0 := by native_decide +revert
  have hplus : ∀ x : ZMod 7, x ^ 3 + 2 ≠ 0 := by native_decide +revert
  have hp_irred : Irreducible p := by
    rw [hp]
    have hmonic : (X ^ 3 - 2 : (ZMod 7)[X]).Monic := by
      change (X ^ 3 - C (2 : ZMod 7)).Monic
      exact Polynomial.monic_X_pow_sub_C 2 (by norm_num)
    have hdeg : (X ^ 3 - 2 : (ZMod 7)[X]).natDegree = 3 := by
      change (X ^ 3 - C (2 : ZMod 7)).natDegree = 3
      exact Polynomial.natDegree_X_pow_sub_C
    have hdeg2 : 2 ≤ (X ^ 3 - 2 : (ZMod 7)[X]).natDegree := by omega
    have hdeg3 : (X ^ 3 - 2 : (ZMod 7)[X]).natDegree ≤ 3 := by omega
    apply (hmonic.irreducible_iff_roots_eq_zero_of_degree_le_three hdeg2 hdeg3).2
    rw [Multiset.eq_zero_iff_forall_notMem]
    intro x hx
    have hroot : Polynomial.eval x (X ^ 3 - 2 : (ZMod 7)[X]) = 0 :=
      (Polynomial.mem_roots hmonic.ne_zero).mp hx
    have hnroot : ∀ x : ZMod 7, Polynomial.eval x (X ^ 3 - 2 : (ZMod 7)[X]) ≠ 0 := by
      simpa using hminus
    exact hnroot x hroot
  have hq_irred : Irreducible q := by
    rw [hq]
    have hmonic : (X ^ 3 + 2 : (ZMod 7)[X]).Monic := by
      change (X ^ 3 + C (2 : ZMod 7)).Monic
      exact Polynomial.monic_X_pow_add_C 2 (by norm_num)
    have hdeg : (X ^ 3 + 2 : (ZMod 7)[X]).natDegree = 3 := by
      change (X ^ 3 + C (2 : ZMod 7)).natDegree = 3
      exact Polynomial.natDegree_X_pow_add_C
    have hdeg2 : 2 ≤ (X ^ 3 + 2 : (ZMod 7)[X]).natDegree := by omega
    have hdeg3 : (X ^ 3 + 2 : (ZMod 7)[X]).natDegree ≤ 3 := by omega
    apply (hmonic.irreducible_iff_roots_eq_zero_of_degree_le_three hdeg2 hdeg3).2
    rw [Multiset.eq_zero_iff_forall_notMem]
    intro x hx
    have hroot : Polynomial.eval x (X ^ 3 + 2 : (ZMod 7)[X]) = 0 :=
      (Polynomial.mem_roots hmonic.ne_zero).mp hx
    have hnroot : ∀ x : ZMod 7, Polynomial.eval x (X ^ 3 + 2 : (ZMod 7)[X]) ≠ 0 := by
      simpa using hplus
    exact hnroot x hroot
  refine ⟨hp_irred, hq_irred, ?_⟩
  exact dummy_assumed (ZMod 7) p q (by simp) hp hq hp_irred hq_irred
