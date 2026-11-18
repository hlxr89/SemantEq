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
  have h := dummy_assumed (ZMod 7) (inferInstance : CharP (ZMod 7) 7)
  refine ⟨h.1, h.2, ?_⟩
  let σ : Polynomial (ZMod 7) →+* Polynomial (ZMod 7) :=
    Polynomial.compRingHom (-X)
  have hσ : Function.Bijective σ := by
    constructor
    · intro a b hab
      have := congrArg (fun r : Polynomial (ZMod 7) => r.comp (-X)) hab
      simpa [σ, Polynomial.comp_assoc] using this
    · intro a
      refine ⟨a.comp (-X), ?_⟩
      simp [σ, Polynomial.comp_assoc]
  let e : Polynomial (ZMod 7) ≃+* Polynomial (ZMod 7) :=
    RingEquiv.ofBijective σ hσ
  refine ⟨Ideal.quotientEquiv
    (span ({X ^ 3 - 2} : Set (Polynomial (ZMod 7))))
    (span ({X ^ 3 + 2} : Set (Polynomial (ZMod 7)))) e ?_⟩
  rw [Ideal.map_span]
  simp only [Set.image_singleton]
  rw [Ideal.span_singleton_eq_span_singleton]
  have he : e (X ^ 3 - 2) = -(X ^ 3 + 2) := by
    simp [e, σ, Polynomial.pow_comp]
    ring
  change Associated (X ^ 3 + 2) (e (X ^ 3 - 2))
  rw [he]
  exact Associated.neg_right (Associated.refl _)
