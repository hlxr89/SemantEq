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
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  subst p
  subst q
  have hp' : Irreducible (X ^ 3 - 2 : Polynomial (ZMod 7)) := by
    apply irreducible_of_degree_le_three_of_not_isRoot (K := ZMod 7)
      (p := (X ^ 3 - 2 : Polynomial (ZMod 7)))
    · rw [show (2 : Polynomial (ZMod 7)) = C 2 by rfl,
        natDegree_X_pow_sub_C]
      norm_num
    · intro x
      fin_cases x <;> simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_ofNat] <;>
        decide
  have hq' : Irreducible (X ^ 3 + 2 : Polynomial (ZMod 7)) := by
    apply irreducible_of_degree_le_three_of_not_isRoot (K := ZMod 7)
      (p := (X ^ 3 + 2 : Polynomial (ZMod 7)))
    · rw [show (2 : Polynomial (ZMod 7)) = C 2 by rfl,
        natDegree_X_pow_add_C]
      norm_num
    · intro x
      fin_cases x <;> simp only [IsRoot, eval_add, eval_pow, eval_X, eval_ofNat] <;>
        decide
  have h := dummy_assumed (F := ZMod 7) (X ^ 3 - 2) (X ^ 3 + 2) hp' hq'
  exact ⟨hp', hq', h.2.2⟩
