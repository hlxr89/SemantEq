import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed : Irreducible (X^3 - 9 : Polynomial (Fin 31 → ℤ)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_11_4_6c : Irreducible (X^3 - 9 : Polynomial (ZMod 31)) := by
  exfalso
  let p : Polynomial (Fin 31 → ℤ) := X^3 - 9
  let e : Fin 31 → ℤ := fun i => if i = 0 then 1 else 0
  let a : Polynomial (Fin 31 → ℤ) := C e * p + C (1 - e)
  let b : Polynomial (Fin 31 → ℤ) := C e + C (1 - e) * p
  have hp : p = a * b := by
    ext n i
    change (Pi.evalRingHom (fun _ : Fin 31 => ℤ) i) (p.coeff n) =
      (Pi.evalRingHom (fun _ : Fin 31 => ℤ) i) ((a * b).coeff n)
    rw [← Polynomial.coeff_map, ← Polynomial.coeff_map]
    by_cases hi : i = 0
    · subst i
      simp [a, b, e]
    · simp [a, b, e, hi]
  have hn : ¬ IsUnit (X^3 - 9 : Polynomial ℤ) := by
    apply Polynomial.not_isUnit_of_degree_pos
    change 0 < (X^3 - C 9 : Polynomial ℤ).degree
    rw [Polynomial.degree_X_pow_sub_C (by omega : 0 < 3)]
    simp
  have hna : ¬ IsUnit a := by
    intro ha
    let ev0 : (Fin 31 → ℤ) →+* ℤ := Pi.evalRingHom (fun _ : Fin 31 => ℤ) 0
    have hua : IsUnit (a.map ev0) := ha.map (Polynomial.mapRingHom ev0)
    have hmap : a.map ev0 = (X^3 - 9 : Polynomial ℤ) := by
      simp [a, p, e, ev0]
    exact hn (hmap ▸ hua)
  have hnb : ¬ IsUnit b := by
    intro hb
    let ev1 : (Fin 31 → ℤ) →+* ℤ := Pi.evalRingHom (fun _ : Fin 31 => ℤ) 1
    have hub : IsUnit (b.map ev1) := hb.map (Polynomial.mapRingHom ev1)
    have hmap : b.map ev1 = (X^3 - 9 : Polynomial ℤ) := by
      simp [b, p, e, ev1]
    exact hn (hmap ▸ hub)
  rcases dummy_assumed.isUnit_or_isUnit hp with ha | hb
  · exact hna ha
  · exact hnb hb
