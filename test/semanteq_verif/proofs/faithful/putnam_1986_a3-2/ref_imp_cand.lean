import Mathlib

open Real

-- ===== unified context (both sides' local defs, merged) =====
noncomputable abbrev putnam_1986_a3_solution : ℝ := Real.pi / 2

-- ===== assumed statement (antecedent) =====
theorem putnam_1986_a3_assumed
(cot : ℝ → ℝ)
(fcot : cot = fun θ ↦ cos θ / sin θ)
(arccot : ℝ → ℝ)
(harccot : ∀ t : ℝ, t ≥ 0 → arccot t ∈ Set.Ioc 0 (Real.pi / 2) ∧ cot (arccot t) = t)
: (∑' n : ℕ, arccot (n ^ 2 + n + 1) = putnam_1986_a3_solution) :=
by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement : ∑' n : ℕ, Real.arctan (1 / ((n : ℝ)^2 + (n : ℝ) + 1)) = π / 2 := by
  let acot : ℝ → ℝ := fun t ↦ if t = 0 then Real.pi / 2 else Real.arctan (1 / t)
  have hacot : ∀ t : ℝ, t ≥ 0 → acot t ∈ Set.Ioc 0 (Real.pi / 2) ∧
      (fun θ : ℝ ↦ Real.cos θ / Real.sin θ) (acot t) = t := by
    intro t ht
    by_cases hzero : t = 0
    · subst t
      constructor
      · simp only [acot, ↓reduceIte, Set.mem_Ioc]
        exact ⟨by positivity, le_rfl⟩
      · simp [acot]
    · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hzero)
      have hinv : 0 < 1 / t := one_div_pos.mpr htpos
      constructor
      · simp only [acot, hzero, ↓reduceIte]
        exact ⟨Real.arctan_pos.mpr hinv, (Real.arctan_lt_pi_div_two _).le⟩
      · simp only [acot, hzero, ↓reduceIte]
        rw [Real.cos_arctan, Real.sin_arctan]
        have hsqrt : 0 < √(1 + (1 / t) ^ 2) := Real.sqrt_pos.2 (by positivity)
        field_simp
  have hsum := putnam_1986_a3_assumed (fun θ : ℝ ↦ Real.cos θ / Real.sin θ) rfl acot hacot
  change ∑' n : ℕ, Real.arctan (1 / ((n : ℝ)^2 + (n : ℝ) + 1)) =
    putnam_1986_a3_solution
  calc
    _ = ∑' n : ℕ, acot (n ^ 2 + n + 1) := by
      apply tsum_congr
      intro n
      have hn : (n : ℝ) ^ 2 + (n : ℝ) + 1 ≠ 0 := by positivity
      simp [acot, hn]
    _ = putnam_1986_a3_solution := hsum

