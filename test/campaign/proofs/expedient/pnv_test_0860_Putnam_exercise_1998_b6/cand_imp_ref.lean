import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (a b c : ℤ) : ∃ (n : ℤ) (H : n > 0), ¬(∃ (m : ℤ), n ^ 3 + a * n ^ 2 + b * n + c = m ^ 2) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1998_b6 (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  let K : ℤ := |a| + |b| + |c| + 1
  let N : ℤ := 4 * K
  have hK : 0 < K := by
    dsimp [K]
    have ha := abs_nonneg a
    have hb := abs_nonneg b
    have hc := abs_nonneg c
    omega
  have hN : 0 < N := by
    dsimp [N]
    omega
  have hpoly : ∀ x : ℤ, K ≤ x → 0 ≤ x ^ 3 + a * x ^ 2 + b * x + c := by
    intro x hx
    have hx0 : 0 ≤ x := le_trans (le_of_lt hK) hx
    have hx1 : 1 ≤ x := by omega
    have ha0 : 0 ≤ |a| := abs_nonneg a
    have hb0 : 0 ≤ |b| := abs_nonneg b
    have hc0 : 0 ≤ |c| := abs_nonneg c
    have ha_le : -|a| ≤ a := neg_abs_le a
    have hb_le : -|b| ≤ b := neg_abs_le b
    have hc_le : -|c| ≤ c := neg_abs_le c
    have hgap : 0 ≤ x - |a| - |b| - |c| - 1 := by
      dsimp [K] at hx
      omega
    have hp : 0 ≤ x ^ 2 * (x - |a| - |b| - |c| - 1) :=
      mul_nonneg (sq_nonneg x) hgap
    have hxsq : x ≤ x ^ 2 := by nlinarith
    have hbmul : 0 ≤ |b| * (x ^ 2 - x) := mul_nonneg hb0 (by omega)
    have hcmul : 0 ≤ |c| * (x ^ 2 - 1) := mul_nonneg hc0 (by omega)
    have hcore : 0 ≤ x ^ 3 - |a| * x ^ 2 - |b| * x - |c| := by
      nlinarith
    have hamul : 0 ≤ (a + |a|) * x ^ 2 :=
      mul_nonneg (by omega) (sq_nonneg x)
    have hbmul' : 0 ≤ (b + |b|) * x := mul_nonneg (by omega) hx0
    have hcmul' : 0 ≤ c + |c| := by omega
    nlinarith
  by_contra h
  push_neg at h
  have hsquare (x : ℤ) (hx : 0 < x) (hKx : K ≤ x) :
      ∃ m : ℤ, x ^ 3 + a * x ^ 2 + b * x + c = m ^ 2 := by
    obtain ⟨m, hm⟩ := h x hx
    refine ⟨m, ?_⟩
    have hp := hpoly x hKx
    have hp' : 0 ≤ ((x ^ 3 + a * x ^ 2 + b * x + c : ℤ) : ℝ) := by
      exact_mod_cast hp
    have heq : ((x ^ 3 + a * x ^ 2 + b * x + c : ℤ) : ℝ) = (m : ℝ) ^ 2 := by
      rw [← Real.sq_sqrt hp']
      simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow] using
        congrArg (fun z : ℝ => z ^ 2) hm
    exact_mod_cast heq
  have hKN : K ≤ N := by
    dsimp [N]
    omega
  obtain ⟨m1, hm1⟩ := hsquare (N + 1) (by omega) (by omega)
  obtain ⟨m2, hm2⟩ := hsquare (N + 2) (by omega) (by omega)
  obtain ⟨m3, hm3⟩ := hsquare (N + 3) (by omega) (by omega)
  obtain ⟨m4, hm4⟩ := hsquare (N + 4) (by omega) (by omega)
  have sqmod (m : ℤ) : m ^ 2 % 4 = 0 ∨ m ^ 2 % 4 = 1 := by
    obtain ⟨k, hk | hk⟩ := Int.even_or_odd' m
    · subst m
      left
      ring_nf
      simp
    · subst m
      right
      rw [show (2 * k + 1) ^ 2 = 4 * (k ^ 2 + k) + 1 by ring]
      omega
  have h1 := sqmod m1
  have h2 := sqmod m2
  have h3 := sqmod m3
  have h4 := sqmod m4
  rw [← hm1] at h1
  rw [← hm2] at h2
  rw [← hm3] at h3
  rw [← hm4] at h4
  dsimp [N] at h1 h2 h3 h4
  ring_nf at h1 h2 h3 h4
  rcases h1 with h1 | h1 <;>
    rcases h2 with h2 | h2 <;>
    rcases h3 with h3 | h3 <;>
    rcases h4 with h4 | h4 <;> omega
