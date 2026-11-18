import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_8_2_4_assumed {R : Type*} [CommRing R] [IsDomain R] [GCDMonoid R]
  (h1 : ∀ a b : R, a ≠ 0 → b ≠ 0 → ∃ r s : R, gcd a b = r*a + s*b)
  (h2 : ∀ a : ℕ → R, (∀ i : ℕ, a i ≠ 0 ∧ a (i + 1) ∣ a i) →
  ∃ N : ℕ, ∀ n ≥ N, ∃ u : R, IsUnit u ∧ a n = u * a N) :
  IsPrincipalIdealRing R := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {R : Type*} [CommRing R] (H : IsDomain R) (H1 : ∀ a b : R, a ≠ 0 → b ≠ 0 → ∃ d x y, d ∣ a ∧ d ∣ b ∧ x * a + y * b = d) (H2 : ∀ a : R, a ≠ 0 → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → IsUnit (a * a^n)) : IsPrincipalIdealRing R := by
  classical
  letI : IsDomain R := H
  let hg : ∀ a b : R, ∃ c : R, ∀ d : R, d ∣ a ∧ d ∣ b ↔ d ∣ c := fun a b ↦ by
    by_cases ha : a = 0
    · exact ⟨b, by simp [ha]⟩
    by_cases hb : b = 0
    · exact ⟨a, by simp [hb]⟩
    obtain ⟨c, x, y, hca, hcb, hxy⟩ := H1 a b ha hb
    refine ⟨c, fun d ↦ ⟨?_, fun hdc ↦ ⟨hdc.trans hca, hdc.trans hcb⟩⟩⟩
    rintro ⟨hda, hdb⟩
    rw [← hxy]
    exact dvd_add (dvd_mul_of_dvd_right hda x) (dvd_mul_of_dvd_right hdb y)
  letI : GCDMonoid R := gcdMonoidOfExistsGCD hg
  apply exercise_8_2_4_assumed
  · intro a b ha hb
    obtain ⟨d, x, y, hda, hdb, hxy⟩ := H1 a b ha hb
    obtain ⟨k, hk⟩ := dvd_gcd hda hdb
    refine ⟨k * x, k * y, ?_⟩
    calc
      gcd a b = d * k := hk
      _ = (k * x) * a + (k * y) * b := by rw [← hxy]; ring
  · intro a ha
    refine ⟨0, fun n hn ↦ ?_⟩
    obtain ⟨n₀, hn₀⟩ := H2 (a 0) (ha 0).1
    have ha0 : IsUnit (a 0) := isUnit_of_mul_isUnit_left (hn₀ n₀ le_rfl)
    obtain ⟨m₀, hm₀⟩ := H2 (a n) (ha n).1
    have han : IsUnit (a n) := isUnit_of_mul_isUnit_left (hm₀ m₀ le_rfl)
    have hinv : (↑(ha0.unit⁻¹) : R) * a 0 = 1 := by
      calc
        (↑(ha0.unit⁻¹) : R) * a 0 = ↑(ha0.unit⁻¹) * ↑ha0.unit :=
          congrArg ((↑(ha0.unit⁻¹) : R) * ·) ha0.unit_spec.symm
        _ = 1 := by simp
    refine ⟨a n * ↑(ha0.unit⁻¹), han.mul (Units.isUnit _), ?_⟩
    rw [mul_assoc, hinv, mul_one]
