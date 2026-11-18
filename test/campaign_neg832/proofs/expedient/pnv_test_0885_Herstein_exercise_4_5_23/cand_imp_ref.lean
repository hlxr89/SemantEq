import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {F : Type*} [Field F] [Fintype F] (f : F[X]) (hf : f.Monic) (h : IsCoprime (X^2 + 2) f) (hprime : Prime (Polynomial.eval 3 f)) : Irreducible f := by
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
  have hirr₁ : Irreducible (X ^ 3 - 2 : (ZMod 7)[X]) := by
    have hm : (X ^ 3 - 2 : (ZMod 7)[X]).Monic := by
      simpa using Polynomial.monic_X_pow_sub_C (2 : ZMod 7) (by norm_num : 3 ≠ 0)
    have hd : (X ^ 3 - 2 : (ZMod 7)[X]).natDegree = 3 := by
      simpa using (Polynomial.natDegree_X_pow_sub_C :
        (X ^ 3 - C (2 : ZMod 7)).natDegree = 3)
    apply (Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three hm
      (by omega) (by omega)).2
    rw [Multiset.eq_zero_iff_forall_notMem]
    intro x
    rw [Polynomial.mem_roots hm.ne_zero]
    unfold Polynomial.IsRoot
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    fin_cases x <;> decide
  have hirr₂ : Irreducible (X ^ 3 + 2 : (ZMod 7)[X]) := by
    have hm : (X ^ 3 + 2 : (ZMod 7)[X]).Monic := by
      simpa using Polynomial.monic_X_pow_add_C (2 : ZMod 7) (by norm_num : 3 ≠ 0)
    have hd : (X ^ 3 + 2 : (ZMod 7)[X]).natDegree = 3 := by
      simpa using (Polynomial.natDegree_X_pow_add_C :
        (X ^ 3 + C (2 : ZMod 7)).natDegree = 3)
    apply (Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three hm
      (by omega) (by omega)).2
    rw [Multiset.eq_zero_iff_forall_notMem]
    intro x
    rw [Polynomial.mem_roots hm.ne_zero]
    unfold Polynomial.IsRoot
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    fin_cases x <;> decide
  refine ⟨hirr₁, hirr₂, ?_⟩
  let e : (ZMod 7)[X] ≃+* (ZMod 7)[X] :=
    { toFun := fun f ↦ f.comp (-X)
      invFun := fun f ↦ f.comp (-X)
      left_inv := Polynomial.comp_neg_X_comp_neg_X
      right_inv := Polynomial.comp_neg_X_comp_neg_X
      map_add' := by intros; exact Polynomial.add_comp
      map_mul' := Polynomial.mul_comp_neg_X }
  refine ⟨Ideal.quotientEquiv (span ({X ^ 3 - 2} : Set (ZMod 7)[X]))
    (span ({X ^ 3 + 2} : Set (ZMod 7)[X])) e ?_⟩
  rw [Ideal.map_span, Set.image_singleton]
  have he : e (X ^ 3 - 2) = -(X ^ 3 + 2) := by
    simp [e]
    ring
  change span ({X ^ 3 + 2} : Set (ZMod 7)[X]) = span ({e (X ^ 3 - 2)} : Set (ZMod 7)[X])
  rw [he]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro x (rfl : x = X ^ 3 + 2)
    exact neg_mem_iff.mp (Ideal.subset_span (Set.mem_singleton _))
  · rw [Ideal.span_le]
    rintro x (rfl : x = -(X ^ 3 + 2))
    exact (span ({X ^ 3 + 2} : Set (ZMod 7)[X])).neg_mem
      (Ideal.subset_span (Set.mem_singleton _))
