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
  have hmonic : Monic (X^4 - 4*X^3 + 6 : Polynomial ℤ) := by
    monicity
    · exact le_trans (le_max_left 4 3) (le_max_left (max 4 3) 0)
    · exact le_trans (le_max_right 4 3) (le_max_left (max 4 3) 0)
  apply hmonic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 2))
  have hirr : Irreducible (X^4 : Polynomial (ZMod 2)) := by
    apply dummy_assumed (X^4 : Polynomial (ZMod 2)) (monic_X_pow 4)
    · rw [degree_X_pow]
      exact WithBot.coe_lt_coe.mpr (Nat.succ_lt_succ (Nat.zero_lt_succ 2))
    · intro x hx
      cases x with
      | zero => exact dvd_zero 2
      | succ x =>
          cases x with
          | zero => exact dvd_zero 2
          | succ x =>
              exact (Nat.not_lt_zero x
                (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hx))).elim
  have h4 : (4 : ZMod 2) = 0 := by rfl
  have h6 : (6 : ZMod 2) = 0 := by rfl
  have hC4 : (4 : Polynomial (ZMod 2)) = 0 := by
    change C (4 : ZMod 2) = 0
    rw [h4, C_0]
  have hC6 : (6 : Polynomial (ZMod 2)) = 0 := by
    change C (6 : ZMod 2) = 0
    rw [h6, C_0]
  simpa only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_natCast, Polynomial.map_ofNat,
    hC4, hC6,
    zero_mul, sub_zero, add_zero] using hirr
