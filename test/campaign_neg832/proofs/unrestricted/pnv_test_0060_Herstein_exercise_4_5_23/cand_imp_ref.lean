import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (F : Type*) [Field F] (hF_char : CharP F 7) : Irreducible (X^3 - 2 : F[X]) ∧ Irreducible (X^3 + 2 : F[X]) := by
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
  have hirr := dummy_assumed (ZMod 7) (ZMod.charP 7)
  refine ⟨hirr.1, hirr.2, ?_⟩
  let e : Polynomial (ZMod 7) ≃ₐ[ZMod 7] Polynomial (ZMod 7) :=
    AlgEquiv.ofAlgHom (aeval (-X)) (aeval (-X)) (by ext <;> simp) (by ext <;> simp)
  refine ⟨(Ideal.quotientEquivAlg
    (span ({X ^ 3 - 2} : Set (Polynomial (ZMod 7))))
    (span ({X ^ 3 + 2} : Set (Polynomial (ZMod 7)))) e ?_).toRingEquiv⟩
  rw [Ideal.map_span]
  have he : e (X ^ 3 - 2) = -(X ^ 3 + 2) := by
    rw [map_sub, map_pow]
    simp only [e, AlgEquiv.ofAlgHom_apply, aeval_X, map_ofNat]
    ring
  simp only [Set.image_singleton]
  change span ({X ^ 3 + 2} : Set (Polynomial (ZMod 7))) =
    span ({e (X ^ 3 - 2)} : Set (Polynomial (ZMod 7)))
  rw [he]
  exact (Ideal.span_singleton_neg (X ^ 3 + 2)).symm
