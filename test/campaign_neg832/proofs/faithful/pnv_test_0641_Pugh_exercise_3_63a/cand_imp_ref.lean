import Mathlib

open Filter Real Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (p : ℝ) (hp : 1 < p) : Summable fun k => 1 / k * (log k) ^ p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_63a (p : ℝ) (f : ℕ → ℝ) (hp : p > 1)
  (h : f = λ (k : ℕ) => (1 : ℝ) / (k * (log k) ^ p)) :
  ∃ l, Tendsto f atTop (𝓝 l) := by
  have hsum : Summable fun k : ℕ => 1 / (k : ℝ) * (log (k : ℝ)) ^ p := by
    simpa [Function.comp_def] using
      (dummy_assumed p hp).comp_injective
        (Nat.cast_injective : Function.Injective (Nat.cast : ℕ → ℝ))
  have hlog : ∀ᶠ k : ℕ in atTop, 1 ≤ log (k : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hk : ∀ᶠ k : ℕ in atTop, 1 ≤ k :=
    Filter.eventually_atTop.2 ⟨1, fun _ hk => hk⟩
  have hnonneg : ∀ᶠ k : ℕ in atTop,
      0 ≤ (1 : ℝ) / (k * (log k) ^ p) := by
    filter_upwards [hlog, hk] with k hlogk hk
    positivity
  have hle : ∀ᶠ k : ℕ in atTop,
      (1 : ℝ) / (k * (log k) ^ p) ≤ 1 / k * (log k) ^ p := by
    filter_upwards [hlog, hk] with k hlogk hk
    have hkp : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
    have hpp : 0 ≤ p := le_trans (by norm_num) (le_of_lt hp)
    have hpow : 1 ≤ (log (k : ℝ)) ^ p := by
      simpa using Real.rpow_le_rpow (by norm_num) hlogk hpp
    have hinv : 1 / (log (k : ℝ)) ^ p ≤ 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hpow
    calc
      (1 : ℝ) / (k * (log k) ^ p) =
          (1 / (log (k : ℝ)) ^ p) * (1 / (k : ℝ)) := by
            simpa using (one_div_mul_one_div_rev ((log (k : ℝ)) ^ p) (k : ℝ)).symm
      _ ≤ 1 * (1 / (k : ℝ)) :=
        mul_le_mul_of_nonneg_right hinv (by positivity)
      _ ≤ (log (k : ℝ)) ^ p * (1 / (k : ℝ)) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = 1 / (k : ℝ) * (log (k : ℝ)) ^ p := by ring
  refine ⟨0, ?_⟩
  rw [h]
  exact squeeze_zero' hnonneg hle hsum.tendsto_atTop_zero
