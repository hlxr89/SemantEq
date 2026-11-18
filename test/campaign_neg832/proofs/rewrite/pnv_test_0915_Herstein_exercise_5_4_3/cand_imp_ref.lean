import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (a : ℂ) (h : a ^ 5 + √(2 : ℝ) * a ^ 3 + √(5 : ℝ) * a ^ 2 + √(7 : ℝ) * a + √(11 : ℝ) = 0) : IsAlgebraic ℚ a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_4_3 {a : ℂ} {p : ℂ → ℂ}
  (hp : p = λ (x : ℂ) => x^5 + sqrt 2 * x^3 + sqrt 5 * x^2 + sqrt 7 * x + sqrt 11)
  (ha : p a = 0) :
  ∃ q : Polynomial ℂ, q ≠ 0 ∧ q.degree ≤ 80 ∧ a ∈ q.roots ∧
  ∀ n : q.support, ∃ a b : ℤ, q.coeff n = a / b := by
  have heq : a ^ 5 + √(2 : ℝ) * a ^ 3 + √(5 : ℝ) * a ^ 2 + √(7 : ℝ) * a + √(11 : ℝ) = 0 := by
    rw [hp] at ha
    exact ha
  have halg : IsAlgebraic ℚ a := dummy_assumed a heq
  let r : Polynomial ℚ := minpoly ℚ a
  let q : Polynomial ℂ := r.map (algebraMap ℚ ℂ)
  have hr0 : r ≠ 0 := minpoly.ne_zero halg.isIntegral
  have hq0 : q ≠ 0 := by
    exact (Polynomial.map_ne_zero_iff (algebraMap ℚ ℂ).injective).mpr hr0
  refine ⟨q, hq0, ?_, ?_, ?_⟩
  · have radical_alg (m : ℕ) : IsAlgebraic ℚ ((√(m : ℝ) : ℝ) : ℂ) := by
      let z : ℂ := ((√(m : ℝ) : ℝ) : ℂ)
      let f : Polynomial ℚ := X ^ 2 - C (m : ℚ)
      have hzsq : z ^ 2 = (m : ℂ) := by
        dsimp only [z]
        exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg m)
      have hf : (aeval z) f = 0 := by
        simp only [f, map_sub, map_pow, aeval_X, aeval_C]
        exact sub_eq_zero.mpr hzsq
      have hf0 : f ≠ 0 := by
        intro hfzero
        have hdeg := congrArg Polynomial.natDegree hfzero
        dsimp only [f] at hdeg
        rw [natDegree_X_pow_sub_C, natDegree_zero] at hdeg
        exact Nat.succ_ne_zero 1 hdeg
      exact ⟨f, hf0, hf⟩
    have radical_finrank (m : ℕ) :
        Module.finrank ℚ (IntermediateField.adjoin ℚ {((√(m : ℝ) : ℝ) : ℂ)}) ≤ 2 := by
      let z : ℂ := ((√(m : ℝ) : ℝ) : ℂ)
      let f : Polynomial ℚ := X ^ 2 - C (m : ℚ)
      have hzalg : IsAlgebraic ℚ z := radical_alg m
      have hzsq : z ^ 2 = (m : ℂ) := by
        dsimp only [z]
        exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg m)
      have hf : (aeval z) f = 0 := by
        simp only [f, map_sub, map_pow, aeval_X, aeval_C]
        exact sub_eq_zero.mpr hzsq
      have hf0 : f ≠ 0 := by
        intro hfzero
        have hdeg := congrArg Polynomial.natDegree hfzero
        dsimp only [f] at hdeg
        rw [natDegree_X_pow_sub_C, natDegree_zero] at hdeg
        exact Nat.succ_ne_zero 1 hdeg
      rw [IntermediateField.adjoin.finrank hzalg.isIntegral]
      have hdvd : minpoly ℚ z ∣ f := minpoly.dvd ℚ z hf
      have hdeg := Polynomial.natDegree_le_of_dvd hdvd hf0
      dsimp only [f] at hdeg
      rwa [natDegree_X_pow_sub_C] at hdeg
    let E2 : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {((√(2 : ℝ) : ℝ) : ℂ)}
    let E5 : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {((√(5 : ℝ) : ℝ) : ℂ)}
    let E7 : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {((√(7 : ℝ) : ℝ) : ℂ)}
    let E11 : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {((√(11 : ℝ) : ℝ) : ℂ)}
    let K25 : IntermediateField ℚ ℂ := E2 ⊔ E5
    let K257 : IntermediateField ℚ ℂ := K25 ⊔ E7
    let K : IntermediateField ℚ ℂ := K257 ⊔ E11
    letI : FiniteDimensional ℚ E2 := IntermediateField.adjoin.finiteDimensional (radical_alg 2).isIntegral
    letI : FiniteDimensional ℚ E5 := IntermediateField.adjoin.finiteDimensional (radical_alg 5).isIntegral
    letI : FiniteDimensional ℚ E7 := IntermediateField.adjoin.finiteDimensional (radical_alg 7).isIntegral
    letI : FiniteDimensional ℚ E11 := IntermediateField.adjoin.finiteDimensional (radical_alg 11).isIntegral
    letI : FiniteDimensional ℚ K25 := IntermediateField.finiteDimensional_sup E2 E5
    letI : FiniteDimensional ℚ K257 := IntermediateField.finiteDimensional_sup K25 E7
    letI : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_sup K257 E11
    have hE2 : Module.finrank ℚ E2 ≤ 2 := radical_finrank 2
    have hE5 : Module.finrank ℚ E5 ≤ 2 := radical_finrank 5
    have hE7 : Module.finrank ℚ E7 ≤ 2 := radical_finrank 7
    have hE11 : Module.finrank ℚ E11 ≤ 2 := radical_finrank 11
    have hK25 : Module.finrank ℚ K25 ≤ 4 := by
      exact (IntermediateField.finrank_sup_le E2 E5).trans (by
        simpa only [Nat.reduceMul] using Nat.mul_le_mul hE2 hE5)
    have hK257 : Module.finrank ℚ K257 ≤ 8 := by
      exact (IntermediateField.finrank_sup_le K25 E7).trans (by
        simpa only [Nat.reduceMul] using Nat.mul_le_mul hK25 hE7)
    have hK : Module.finrank ℚ K ≤ 16 := by
      exact (IntermediateField.finrank_sup_le K257 E11).trans (by
        simpa only [Nat.reduceMul] using Nat.mul_le_mul hK257 hE11)
    have hz2K : ((√(2 : ℝ) : ℝ) : ℂ) ∈ K := by
      apply (show E2 ≤ K from le_trans le_sup_left (le_trans le_sup_left le_sup_left))
      exact IntermediateField.mem_adjoin_simple_self ℚ _
    have hz5K : ((√(5 : ℝ) : ℝ) : ℂ) ∈ K := by
      apply (show E5 ≤ K from le_trans le_sup_right (le_trans le_sup_left le_sup_left))
      exact IntermediateField.mem_adjoin_simple_self ℚ _
    have hz7K : ((√(7 : ℝ) : ℝ) : ℂ) ∈ K := by
      apply (show E7 ≤ K from le_trans le_sup_right le_sup_left)
      exact IntermediateField.mem_adjoin_simple_self ℚ _
    have hz11K : ((√(11 : ℝ) : ℝ) : ℂ) ∈ K := by
      apply (show E11 ≤ K from le_sup_right)
      exact IntermediateField.mem_adjoin_simple_self ℚ _
    let z2 : K := ⟨((√(2 : ℝ) : ℝ) : ℂ), hz2K⟩
    let z5 : K := ⟨((√(5 : ℝ) : ℝ) : ℂ), hz5K⟩
    let z7 : K := ⟨((√(7 : ℝ) : ℝ) : ℂ), hz7K⟩
    let z11 : K := ⟨((√(11 : ℝ) : ℝ) : ℂ), hz11K⟩
    let gK : Polynomial K := C z2 * X ^ 3 + C z5 * X ^ 2 + C z7 * X + C z11
    let fK : Polynomial K := X ^ 5 + gK
    have hgKnat : gK.natDegree ≤ 3 := by
      dsimp only [gK]
      apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le
      · apply (Polynomial.natDegree_add_le _ _).trans
        apply max_le
        · apply (Polynomial.natDegree_add_le _ _).trans
          apply max_le
          · exact Polynomial.natDegree_C_mul_X_pow_le z2 3
          · exact (Polynomial.natDegree_C_mul_X_pow_le z5 2).trans (by
              exact Nat.le_succ 2)
        · rw [← pow_one X]
          exact (Polynomial.natDegree_C_mul_X_pow_le z7 1).trans (by
            exact (Nat.le_succ 1).trans (Nat.le_succ 2))
      · rw [Polynomial.natDegree_C]
        exact Nat.zero_le 3
    have hgKdeg : gK.degree < (X ^ 5 : Polynomial K).degree := by
      rw [Polynomial.degree_X_pow]
      exact (Polynomial.degree_le_natDegree.trans_lt
        (WithBot.coe_lt_coe.mpr (hgKnat.trans_lt (show 3 < 5 from Nat.le_succ 4)) :
          (gK.natDegree : WithBot ℕ) < (5 : WithBot ℕ)))
    have hfKmonic : fK.Monic := by
      dsimp only [fK]
      exact (monic_X_pow 5).add_of_left hgKdeg
    have hfKa : (aeval a) fK = 0 := by
      dsimp only [fK, gK]
      rw [Polynomial.aeval_def]
      simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]
      change a ^ 5 + ((z2 : ℂ) * a ^ 3 + (z5 : ℂ) * a ^ 2 + (z7 : ℂ) * a + (z11 : ℂ)) = 0
      dsimp only [z2, z5, z7, z11]
      simpa only [add_assoc] using heq
    have haKalg : IsAlgebraic K a := ⟨fK, hfKmonic.ne_zero, hfKa⟩
    let E : IntermediateField K ℂ := IntermediateField.adjoin K {a}
    letI : Algebra ℚ E := ((algebraMap K E).comp (algebraMap ℚ K)).toAlgebra
    letI : IsScalarTower ℚ K E := IsScalarTower.of_algebraMap_eq fun _ => rfl
    letI : FiniteDimensional K E := IntermediateField.adjoin.finiteDimensional haKalg.isIntegral
    letI : FiniteDimensional ℚ E := FiniteDimensional.trans ℚ K E
    have hfKnat : fK.natDegree = 5 := by
      apply Polynomial.natDegree_eq_of_degree_eq_some
      dsimp only [fK]
      rw [Polynomial.degree_add_eq_left_of_degree_lt hgKdeg, Polynomial.degree_X_pow]
    have hKE : Module.finrank K E ≤ 5 := by
      rw [IntermediateField.adjoin.finrank haKalg.isIntegral]
      have hdvd : minpoly K a ∣ fK := minpoly.dvd K a hfKa
      have hdeg := Polynomial.natDegree_le_of_dvd hdvd hfKmonic.ne_zero
      rwa [hfKnat] at hdeg
    have hQE : Module.finrank ℚ E ≤ 80 := by
      rw [← Module.finrank_mul_finrank ℚ K E]
      simpa only [Nat.reduceMul] using Nat.mul_le_mul hK hKE
    let aE : E := ⟨a, IntermediateField.mem_adjoin_simple_self K a⟩
    have hdegE : (minpoly ℚ aE).natDegree ≤ Module.finrank ℚ E := minpoly.natDegree_le aE
    have hmin : minpoly ℚ a = minpoly ℚ aE := by
      exact minpoly.algHom_eq (E.val.restrictScalars ℚ) E.val.injective aE
    have hrdeg : r.natDegree ≤ 80 := by
      dsimp only [r]
      rw [hmin]
      exact hdegE.trans hQE
    dsimp only [q]
    rw [Polynomial.degree_map_eq_of_injective (algebraMap ℚ ℂ).injective]
    rw [Polynomial.degree_eq_natDegree hr0]
    exact_mod_cast hrdeg
  · rw [mem_roots hq0]
    dsimp only [q]
    change (Polynomial.map (algebraMap ℚ ℂ) r).eval a = 0
    rw [eval_map]
    change (aeval a) r = 0
    dsimp only [r]
    exact minpoly.aeval ℚ a
  · intro n
    let c : ℚ := r.coeff n
    refine ⟨c.num, c.den, ?_⟩
    dsimp only [q]
    rw [coeff_map]
    change (algebraMap ℚ ℂ) c = (c.num : ℂ) / (c.den : ℂ)
    have hc := congrArg (algebraMap ℚ ℂ) (Rat.num_div_den c).symm
    simpa only [map_div₀, map_intCast] using hc
