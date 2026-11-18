import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a b c : ℤ} : ∃ n : ℕ, ¬∃ m : ℕ, m^2 = n^3 + a * n^2 + b * n + c := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1998_b6 (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  let k : ℕ := a.natAbs + b.natAbs + c.natAbs + 1
  let A : ℤ := 3 * (k : ℤ) + a
  let B : ℤ := 3 * (k : ℤ)^2 + 2 * a * (k : ℤ) + b
  let C : ℤ := (k : ℤ)^3 + a * (k : ℤ)^2 + b * (k : ℤ) + c
  obtain ⟨n, hn⟩ := (dummy_assumed (a := A) (b := B) (c := C))
  refine ⟨(n + k : ℕ), ?_, ?_⟩
  · exact_mod_cast (show 0 < n + k by
      dsimp only [k]
      -- non-rewrite step: the translated natural witness is positive
      omega)
  · rintro ⟨m, hm⟩
    have htranslate :
        ((n + k : ℕ) : ℤ)^3 + a * ((n + k : ℕ) : ℤ)^2 +
            b * ((n + k : ℕ) : ℤ) + c =
          (n : ℤ)^3 + A * (n : ℤ)^2 + B * (n : ℤ) + C := by
      dsimp only [A, B, C]
      push_cast
      -- non-rewrite step: expand the translated cubic
      ring
    have hkbound : a.natAbs + b.natAbs + c.natAbs < k := by
      dsimp only [k]
      exact Nat.lt_add_one _
    have hkpos : 0 < (k : ℤ) := by
      exact_mod_cast Nat.zero_lt_of_lt hkbound
    have hvaluepos :
        0 < ((n + k : ℕ) : ℤ)^3 + a * ((n + k : ℕ) : ℤ)^2 +
          b * ((n + k : ℕ) : ℤ) + c := by
      have ha : -(k : ℤ) < a := by
        -- non-rewrite step: extract a coefficient bound from the definition of k
        have haNat : a.natAbs < k := by omega
        have haAbs : |a| < (k : ℤ) := by
          rw [← Int.natCast_natAbs]
          exact_mod_cast haNat
        exact neg_lt_of_abs_lt haAbs
      have hb : -(k : ℤ) < b := by
        -- non-rewrite step: extract a coefficient bound from the definition of k
        have hbNat : b.natAbs < k := by omega
        have hbAbs : |b| < (k : ℤ) := by
          rw [← Int.natCast_natAbs]
          exact_mod_cast hbNat
        exact neg_lt_of_abs_lt hbAbs
      have hc : -(k : ℤ) < c := by
        -- non-rewrite step: extract a coefficient bound from the definition of k
        have hcNat : c.natAbs < k := by omega
        have hcAbs : |c| < (k : ℤ) := by
          rw [← Int.natCast_natAbs]
          exact_mod_cast hcNat
        exact neg_lt_of_abs_lt hcAbs
      have hnnonneg : 0 ≤ (n : ℤ) := by positivity
      have hnk : (k : ℤ) ≤ ((n + k : ℕ) : ℤ) := by
        -- non-rewrite step: the translated argument is at least the shift
        omega
      -- non-rewrite step: the translated cubic is positive past the coefficient bound
      nlinarith [sq_nonneg (((n + k : ℕ) : ℤ) - 1)]
    apply hn
    have hmnonneg : 0 ≤ m := by
      have hmnonnegR : (0 : ℝ) ≤ (m : ℝ) := by
        rw [← hm]
        exact Real.sqrt_nonneg _
      exact_mod_cast hmnonnegR
    refine ⟨m.natAbs, ?_⟩
    have hsquare : (m : ℝ)^2 =
        (((n + k : ℕ) : ℤ)^3 + a * ((n + k : ℕ) : ℤ)^2 +
          b * ((n + k : ℕ) : ℤ) + c : ℤ) := by
      have hsquareR := congrArg (fun x : ℝ => x^2) hm
      dsimp only at hsquareR
      have hvalueNonnegR :
          0 ≤ (((n + k : ℕ) : ℤ) : ℝ)^3 + (a : ℝ) * (((n + k : ℕ) : ℤ) : ℝ)^2 +
            (b : ℝ) * (((n + k : ℕ) : ℤ) : ℝ) + (c : ℝ) := by
        exact_mod_cast le_of_lt hvaluepos
      rw [Real.sq_sqrt hvalueNonnegR] at hsquareR
      simp only [Int.cast_add, Int.cast_mul, Int.cast_pow]
      exact hsquareR.symm
    have hsquareZ : m^2 =
        ((n + k : ℕ) : ℤ)^3 + a * ((n + k : ℕ) : ℤ)^2 +
          b * ((n + k : ℕ) : ℤ) + c := by
      exact_mod_cast hsquare
    rw [htranslate] at hsquareZ
    rw [Int.natCast_natAbs, abs_of_nonneg hmnonneg]
    exact hsquareZ
