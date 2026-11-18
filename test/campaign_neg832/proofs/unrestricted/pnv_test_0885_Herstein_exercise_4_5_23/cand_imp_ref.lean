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
  subst p
  subst q
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hp_irred : Irreducible (X^3 - 2 : Polynomial (ZMod 7)) := by
    apply @irreducible_of_degree_le_three_of_not_isRoot (ZMod 7) _ (X^3 - 2)
    · change (X^3 - C 2 : Polynomial (ZMod 7)).natDegree ∈ Finset.Icc 1 3
      rw [natDegree_X_pow_sub_C]
      decide
    · intro x
      fin_cases x <;> simp [IsRoot] <;> decide
  have hq_irred : Irreducible (X^3 + 2 : Polynomial (ZMod 7)) := by
    apply @irreducible_of_degree_le_three_of_not_isRoot (ZMod 7) _ (X^3 + 2)
    · change (X^3 + C 2 : Polynomial (ZMod 7)).natDegree ∈ Finset.Icc 1 3
      rw [natDegree_X_pow_add_C]
      decide
    · intro x
      fin_cases x <;> simp [IsRoot] <;> decide
  refine ⟨hp_irred, hq_irred, ?_⟩
  let σ : Polynomial (ZMod 7) →+* Polynomial (ZMod 7) :=
    eval₂RingHom C (-X)
  have hσ : σ.comp σ = RingHom.id (Polynomial (ZMod 7)) := by
    ext <;> simp [σ]
  let e : Polynomial (ZMod 7) ≃+* Polynomial (ZMod 7) :=
    { σ with
      invFun := σ
      left_inv := fun f => DFunLike.congr_fun hσ f
      right_inv := fun f => DFunLike.congr_fun hσ f }
  refine ⟨Ideal.quotientEquiv
    (span ({X^3 - 2} : Set $ Polynomial $ ZMod 7))
    (span ({X^3 + 2} : Set $ Polynomial $ ZMod 7)) e ?_⟩
  rw [Ideal.map_span]
  change span ({X^3 + 2} : Set $ Polynomial $ ZMod 7) =
    span (e '' ({X^3 - 2} : Set $ Polynomial $ ZMod 7))
  simp only [Set.image_singleton]
  rw [Ideal.span_singleton_eq_span_singleton]
  change Associated (X^3 + 2 : Polynomial (ZMod 7)) (σ (X^3 - 2))
  simp only [map_sub, map_pow]
  have hx : σ X = -X := by simp [σ]
  have h2 : σ 2 = 2 := by norm_num [σ]
  rw [hx, h2]
  rw [show (-X : Polynomial (ZMod 7)) ^ 3 - 2 = -(X^3 + 2) by ring]
  exact Associated.rfl.neg_right
