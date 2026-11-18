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
  let e : ZMod 7 ≃+* F := ZMod.ringEquivOfPrime F (by norm_num) hF
  let ep : (ZMod 7)[X] ≃+* F[X] := Polynomial.mapEquiv e
  let p₀ : (ZMod 7)[X] := X ^ 3 - 2
  let q₀ : (ZMod 7)[X] := X ^ 3 + 2
  obtain ⟨_, _, ⟨h⟩⟩ := exercise_4_5_23_assumed (p := p₀) (q := q₀) rfl rfl
  have hep : ep p₀ = p := by simp [ep, p₀, hp]
  have heq : ep q₀ = q := by simp [ep, q₀, hq]
  have hIp : Ideal.span ({p} : Set F[X]) =
      (Ideal.span ({p₀} : Set (ZMod 7)[X])).map ep.toRingHom := by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {p} = Ideal.span {ep p₀}
    rw [hep]
  have hIq : Ideal.span ({q} : Set F[X]) =
      (Ideal.span ({q₀} : Set (ZMod 7)[X])).map ep.toRingHom := by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {q} = Ideal.span {ep q₀}
    rw [heq]
  let Ep := Ideal.quotientEquiv (Ideal.span ({p₀} : Set (ZMod 7)[X]))
    (Ideal.span ({p} : Set F[X])) ep hIp
  let Eq := Ideal.quotientEquiv (Ideal.span ({q₀} : Set (ZMod 7)[X]))
    (Ideal.span ({q} : Set F[X])) ep hIq
  exact ⟨Ep.symm.trans (h.trans Eq)⟩
