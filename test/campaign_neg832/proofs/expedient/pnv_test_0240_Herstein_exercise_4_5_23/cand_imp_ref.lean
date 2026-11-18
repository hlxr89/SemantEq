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
  subst p
  subst q
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hp_irred : Irreducible (X ^ 3 - 2 : (ZMod 7)[X]) := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot (K := ZMod 7)
    · have hd : (X ^ 3 - 2 : (ZMod 7)[X]).natDegree = 3 :=
        Polynomial.natDegree_sub_eq_left_of_natDegree_lt
          (p := (X ^ 3 : (ZMod 7)[X])) (q := 2) (by norm_num) |>.trans
            (Polynomial.natDegree_X_pow 3)
      simp [hd]
    · intro x hx
      fin_cases x <;> norm_num [Polynomial.IsRoot, Polynomial.eval_sub] at hx
      all_goals revert hx; native_decide
  have hq_irred : Irreducible (X ^ 3 + 2 : (ZMod 7)[X]) := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot (K := ZMod 7)
    · have hd : (X ^ 3 + 2 : (ZMod 7)[X]).natDegree = 3 :=
        Polynomial.natDegree_add_eq_left_of_natDegree_lt
          (p := (X ^ 3 : (ZMod 7)[X])) (q := 2) (by norm_num) |>.trans
            (Polynomial.natDegree_X_pow 3)
      simp [hd]
    · intro x hx
      fin_cases x <;> norm_num [Polynomial.IsRoot, Polynomial.eval_add] at hx
      all_goals revert hx; native_decide
  exact ⟨hp_irred, hq_irred,
    dummy_assumed (ZMod 7) (X ^ 3 - 2) (X ^ 3 + 2) (by simp) rfl rfl hp_irred hq_irred⟩
