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
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  subst p
  subst q
  have hp_irred : Irreducible (X ^ 3 - 2 : (ZMod 7)[X]) := by
    have hm : (X ^ 3 - 2 : (ZMod 7)[X]).Monic := by monicity <;> norm_num
    have hd : (X ^ 3 - 2 : (ZMod 7)[X]).natDegree = 3 := by
      compute_degree <;> exact one_ne_zero
    rw [hm.irreducible_iff_roots_eq_zero_of_degree_le_three
      (by omega) (by omega)]
    have hn : ∀ x : ZMod 7, x ^ 3 - 2 ≠ 0 := by native_decide
    apply Multiset.eq_zero_of_forall_notMem
    intro x hx
    rw [Polynomial.mem_roots hm.ne_zero] at hx
    exact hn x (by simpa [Polynomial.IsRoot] using hx)
  have hq_irred : Irreducible (X ^ 3 + 2 : (ZMod 7)[X]) := by
    have hm : (X ^ 3 + 2 : (ZMod 7)[X]).Monic := by monicity <;> norm_num
    have hd : (X ^ 3 + 2 : (ZMod 7)[X]).natDegree = 3 := by
      compute_degree <;> exact one_ne_zero
    rw [hm.irreducible_iff_roots_eq_zero_of_degree_le_three
      (by omega) (by omega)]
    have hn : ∀ x : ZMod 7, x ^ 3 + 2 ≠ 0 := by native_decide
    apply Multiset.eq_zero_of_forall_notMem
    intro x hx
    rw [Polynomial.mem_roots hm.ne_zero] at hx
    exact hn x (by simpa [Polynomial.IsRoot] using hx)
  refine ⟨hp_irred, hq_irred, ?_⟩
  exact dummy_assumed (ZMod 7) (X ^ 3 - 2) (X ^ 3 + 2) (ZMod.card 7) rfl rfl
    hp_irred hq_irred
