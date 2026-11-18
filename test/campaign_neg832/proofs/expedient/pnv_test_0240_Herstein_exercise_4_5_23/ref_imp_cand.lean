import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_5_23_assumed {p q: Polynomial (ZMod 7)}
  (hp : p = X^3 - 2) (hq : q = X^3 + 2) :
  Irreducible p ∧ Irreducible q ∧
  (Nonempty $ Polynomial (ZMod 7) ⧸ span ({p} : Set $ Polynomial $ ZMod 7) ≃+*
  Polynomial (ZMod 7) ⧸ span ({q} : Set $ Polynomial $ ZMod 7)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (F : Type*) [Field F] [Fintype F] (p q : F[X]) (hF : Fintype.card F = 7) (hp : p = X ^ 3 - 2) (hq : q = X ^ 3 + 2) (hp_irred : Irreducible p) (hq_irred : Irreducible q) : Nonempty (F[X] ⧸ Ideal.span {p} ≃+* F[X] ⧸ Ideal.span {q}) := by
  let e : F[X] ≃ₐ[F] F[X] :=
    AlgEquiv.ofAlgHom (aeval (-X)) (aeval (-X)) (by ext <;> simp) (by ext <;> simp)
  refine ⟨Ideal.quotientEquiv (Ideal.span {p}) (Ideal.span {q}) e.toRingEquiv ?_⟩
  subst p
  subst q
  rw [Ideal.map_span]
  simp only [Set.image_singleton]
  have he : e (X ^ 3 - 2) = -(X ^ 3 + 2) := by
    dsimp [e]
    rw [map_sub, map_pow, aeval_X, map_ofNat]
    ring
  change Ideal.span {(X ^ 3 + 2 : F[X])} = Ideal.span {e (X ^ 3 - 2)}
  rw [he]
  exact Ideal.span_singleton_eq_span_singleton.mpr
    ((Associated.refl (X ^ 3 + 2 : F[X])).neg_right)
