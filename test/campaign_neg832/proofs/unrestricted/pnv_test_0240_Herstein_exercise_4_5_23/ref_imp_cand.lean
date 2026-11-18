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
  subst p
  subst q
  let e : ZMod 7 ≃+* F := ZMod.ringEquivOfPrime F (by norm_num) hF
  let pe : (ZMod 7)[X] ≃+* F[X] := Polynomial.mapEquiv e
  have hpmap : pe (X ^ 3 - 2) = X ^ 3 - 2 := by
    simp [pe, e]
  have hqmap : pe (X ^ 3 + 2) = X ^ 3 + 2 := by
    simp [pe, e]
  have hIp : Ideal.span ({X ^ 3 - 2} : Set F[X]) =
      (Ideal.span ({X ^ 3 - 2} : Set (ZMod 7)[X])).map pe.toRingHom := by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {X ^ 3 - 2} = Ideal.span {pe (X ^ 3 - 2)}
    rw [hpmap]
  have hIq : Ideal.span ({X ^ 3 + 2} : Set F[X]) =
      (Ideal.span ({X ^ 3 + 2} : Set (ZMod 7)[X])).map pe.toRingHom := by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {X ^ 3 + 2} = Ideal.span {pe (X ^ 3 + 2)}
    rw [hqmap]
  obtain ⟨_, _, h⟩ := exercise_4_5_23_assumed (p := X ^ 3 - 2) (q := X ^ 3 + 2) rfl rfl
  exact ⟨(Ideal.quotientEquiv _ _ pe hIp).symm |>.trans
    (h.some.trans (Ideal.quotientEquiv _ _ pe hIq))⟩
