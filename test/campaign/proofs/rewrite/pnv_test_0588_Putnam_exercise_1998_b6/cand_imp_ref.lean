import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (a b c : ℤ) : ∃ n : ℕ, 0 < n ∧ ¬ ∃ k : ℤ, k^2 = n^3 + a * n^2 + b * n + c := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1998_b6 (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  let t : ℤ := |a| + |b| + |c| + 1
  obtain ⟨y, hy, hnonsq⟩ :=
    dummy_assumed (3 * t + a) (3 * t^2 + 2 * a * t + b)
      (t^3 + a * t^2 + b * t + c)
  let x : ℤ := y + t
  have hpositive : 0 < x ∧ 0 < x^3 + a*x^2 + b*x + c := by -- non-rewrite step
    have hy' : (0 : ℤ) < (y : ℤ) := by exact_mod_cast hy
    have ha0 : 0 ≤ |a| := abs_nonneg a
    have hb0 : 0 ≤ |b| := abs_nonneg b
    have hc0 : 0 ≤ |c| := abs_nonneg c
    have hxa : |a| < x := by
      dsimp [x, t]
      omega
    have hxb : |b| < x := by
      dsimp [x, t]
      omega
    have hxc : |c| < x := by
      dsimp [x, t]
      omega
    have ha : -x + 1 ≤ a := by
      have haa := neg_abs_le a
      omega
    have hb : -x + 1 ≤ b := by
      have hbb := neg_abs_le b
      omega
    have hc : -x + 1 ≤ c := by
      have hcc := neg_abs_le c
      omega
    have hx : 0 < x := by
      dsimp [x, t]
      omega
    have hx0 : 0 ≤ x := le_of_lt hx
    have hx20 : 0 ≤ x^2 := sq_nonneg x
    have ha' : (-x + 1) * x^2 ≤ a * x^2 :=
      mul_le_mul_of_nonneg_right ha hx20
    have hb' : (-x + 1) * x ≤ b * x :=
      mul_le_mul_of_nonneg_right hb hx0
    constructor
    · exact hx
    · nlinarith
  obtain ⟨hx, hrad⟩ := hpositive
  refine ⟨x, hx, ?_⟩
  rintro ⟨m, hm⟩
  apply hnonsq
  refine ⟨m, ?_⟩
  have hm2 : (m : ℝ)^2 = x^3 + a*x^2 + b*x + c := by
    rw [← hm]
    exact Real.sq_sqrt (by exact_mod_cast le_of_lt hrad)
  have htranslate :
      x^3 + a*x^2 + b*x + c =
        (y : ℤ)^3 + (3 * t + a) * (y : ℤ)^2 +
          (3 * t^2 + 2 * a * t + b) * (y : ℤ) +
          (t^3 + a * t^2 + b * t + c) := by -- non-rewrite step
    dsimp [x]
    ring
  rw [← htranslate]
  exact_mod_cast hm2
