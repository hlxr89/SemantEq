import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} [Fact (Nat.Prime p)] (f : Polynomial (ZMod p)) (hf : f.Monic) (hfd : f.degree > 1) (hp : ∀ (x : ℕ), x < p → p ∣ x^p - x) : Irreducible f := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_4_2a : Irreducible (X^4 - 4*X^3 + 6 : Polynomial ℤ) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : Polynomial (ZMod 2) :=
    (X^4 - 4*X^3 + 6 : Polynomial ℤ).map (Int.castRingHom (ZMod 2))
  have hlow : (C 4 * X^3 - C 6 : Polynomial ℤ).degree < 4 := by
    calc
      (C 4 * X^3 - C 6 : Polynomial ℤ).degree ≤
          max (C 4 * X^3 : Polynomial ℤ).degree (C 6 : Polynomial ℤ).degree :=
        Polynomial.degree_sub_le _ _
      _ = 3 := by
        rw [Polynomial.degree_C_mul_X_pow 3 (by norm_num),
          Polynomial.degree_C (by norm_num)]
        norm_num
      _ < 4 := by norm_num
  have hmon : (X^4 - 4*X^3 + 6 : Polynomial ℤ).Monic := by
    rw [show (4 : Polynomial ℤ) = C 4 by norm_num]
    rw [show (6 : Polynomial ℤ) = C 6 by norm_num]
    convert Polynomial.monic_X_pow_sub (R := ℤ) (n := 4)
      (p := C 4 * X^3 - C 6) hlow using 1 <;> ring
  have hdeg : (X^4 - 4*X^3 + 6 : Polynomial ℤ).degree = 4 := by
    rw [show (4 : Polynomial ℤ) = C 4 by norm_num]
    rw [show (6 : Polynomial ℤ) = C 6 by norm_num]
    rw [show (X^4 - C 4 * X^3 + C 6 : Polynomial ℤ) =
      X^4 - (C 4 * X^3 - C 6) by ring]
    rw [Polynomial.degree_sub_eq_left_of_degree_lt]
    · exact Polynomial.degree_X_pow 4
    · simpa [Polynomial.degree_X_pow] using hlow
  have hf : f.Monic := hmon.map (Int.castRingHom (ZMod 2))
  have hfd : f.degree > 1 := by
    rw [show f.degree = (X^4 - 4*X^3 + 6 : Polynomial ℤ).degree from
      hmon.degree_map (Int.castRingHom (ZMod 2))]
    rw [hdeg]
    norm_num
  have hp : ∀ (x : ℕ), x < 2 → 2 ∣ x^2 - x := by
    intro x hx
    interval_cases x <;> norm_num
  exact hmon.irreducible_of_irreducible_map (Int.castRingHom (ZMod 2)) _
    (dummy_assumed f hf hfd hp)
