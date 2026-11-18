import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {F : Type u} [Field F] (p q : F[X]) (hp : Irreducible p) (hq : Irreducible q) : IsField (F[X] ⧸ Ideal.span {p}) ∧ IsField (F[X] ⧸ Ideal.span {q}) ∧ Nonempty (F[X] ⧸ Ideal.span {p} ≃+* F[X] ⧸ Ideal.span {q}) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_5_23 {p q: Polynomial (ZMod 7)}
  (hp : p = X^3 - 2) (hq : q = X^3 + 2) :
  Irreducible p ∧ Irreducible q ∧
  (Nonempty $ Polynomial (ZMod 7) ⧸ span ({p} : Set $ Polynomial $ ZMod 7) ≃+*
  Polynomial (ZMod 7) ⧸ span ({q} : Set $ Polynomial $ ZMod 7)) := by
  have hdegQ : ((X ^ 2 + X + 1) : (ZMod 2)[X]).natDegree = 2 := by
    compute_degree <;> norm_num
  have hq2 : Irreducible ((X ^ 2 + X + 1) : (ZMod 2)[X]) := by
    apply irreducible_of_degree_le_three_of_not_isRoot
    · rw [Finset.mem_Icc, hdegQ]
      norm_num
    · intro x
      fin_cases x <;> norm_num [IsRoot, eval] <;> decide
  obtain ⟨_, _, ⟨e⟩⟩ := dummy_assumed (X : (ZMod 2)[X]) (X ^ 2 + X + 1) irreducible_X hq2
  have hc := Nat.card_congr e.toEquiv
  letI : Module.Finite (ZMod 2) ((ZMod 2)[X] ⧸ Ideal.span ({(X : (ZMod 2)[X])} : Set (ZMod 2)[X])) :=
    monic_X.finite_quotient
  have hmonic : Monic ((X ^ 2 + X + 1) : (ZMod 2)[X]) := by
    monicity <;> norm_num
  letI : Module.Finite (ZMod 2) ((ZMod 2)[X] ⧸ Ideal.span ({((X ^ 2 + X + 1) : (ZMod 2)[X])} : Set (ZMod 2)[X])) :=
    hmonic.finite_quotient
  have hcX : Nat.card ((ZMod 2)[X] ⧸ Ideal.span ({(X : (ZMod 2)[X])} : Set (ZMod 2)[X])) = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), finrank_quotient_span_eq_natDegree]
    norm_num
  have hcQ : Nat.card ((ZMod 2)[X] ⧸ Ideal.span ({((X ^ 2 + X + 1) : (ZMod 2)[X])} : Set (ZMod 2)[X])) = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), finrank_quotient_span_eq_natDegree]
    norm_num [hdegQ]
  rw [hcX, hcQ] at hc
  norm_num at hc

