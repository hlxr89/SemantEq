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
  letI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  letI : CharP F 7 := charP_of_card_eq_prime hF
  letI : Algebra (ZMod 7) F := ZMod.algebra F 7
  let e : F ≃+* ZMod 7 :=
    (FiniteField.algEquivOfCardEq 7 (K := F) (K' := ZMod 7) (by rw [hF, ZMod.card])).toRingEquiv
  let pe : F[X] ≃+* (ZMod 7)[X] := Polynomial.mapEquiv e
  have hpmap : pe p = X ^ 3 - 2 := by
    simpa only [pe, Polynomial.mapEquiv_apply, map_sub, map_pow, map_ofNat,
      Polynomial.map_X] using congrArg pe hp
  have hqmap : pe q = X ^ 3 + 2 := by
    simpa only [pe, Polynomial.mapEquiv_apply, map_add, map_pow, map_ofNat,
      Polynomial.map_X] using congrArg pe hq
  obtain ⟨_, _, hiso⟩ := exercise_4_5_23_assumed hpmap hqmap
  have hIp : Ideal.span {pe p} = (Ideal.span {p}).map (pe : F[X] →+* (ZMod 7)[X]) := by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {pe p} = Ideal.span {pe p}
    exact rfl
  have hIq : Ideal.span {pe q} = (Ideal.span {q}).map (pe : F[X] →+* (ZMod 7)[X]) := by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {pe q} = Ideal.span {pe q}
    exact rfl
  exact Nonempty.map (fun iso ↦
    (Ideal.quotientEquiv (Ideal.span {p}) (Ideal.span {pe p}) pe hIp).trans
      (iso.trans
        (Ideal.quotientEquiv (Ideal.span {q}) (Ideal.span {pe q}) pe hIq).symm)) hiso
