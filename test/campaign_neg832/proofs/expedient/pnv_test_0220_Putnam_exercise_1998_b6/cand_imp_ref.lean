import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a b c : ℤ} : ∃ (n : ℕ) (H : 0 < n), ¬(n : ℝ) ^ 3 + a * n ^ 2 + b * n + c = 0 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1998_b6 (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  let S : ℤ := |a| + |b| + |c| + 2
  have hS : 2 ≤ S := by
    dsimp [S]
    have := abs_nonneg a
    have := abs_nonneg b
    have := abs_nonneg c
    omega
  have hpos : ∀ x : ℤ, 2 * S ≤ x → 0 < x^3 + a*x^2 + b*x + c := by
    intro x hx
    have hx0 : 0 ≤ x := by nlinarith
    have ha : -S ≤ a := by
      have haa := neg_abs_le a
      have hab := abs_nonneg b
      have hac := abs_nonneg c
      dsimp [S]
      omega
    have hb : -S ≤ b := by
      have hbb := neg_abs_le b
      have haa := abs_nonneg a
      have hac := abs_nonneg c
      dsimp [S]
      omega
    have hc : -S ≤ c := by
      have hcc := neg_abs_le c
      have haa := abs_nonneg a
      have hab := abs_nonneg b
      dsimp [S]
      omega
    have hxa : 0 ≤ (a + S) * x^2 := mul_nonneg (by omega) (sq_nonneg x)
    have hxb : 0 ≤ (b + S) * x := mul_nonneg (by omega) hx0
    have hxc : 0 ≤ c + S := by omega
    have hbig : 0 ≤ (x - 2*S) * x^2 := mul_nonneg (by omega) (sq_nonneg x)
    have hx4 : 4 ≤ x := by nlinarith
    have hquad : 0 < x^2 - x - 1 := by nlinarith
    have hlast : 0 < S * (x^2 - x - 1) := mul_pos (by omega) hquad
    nlinarith
  let r : ℤ := if b % 2 = 0 then 2*S + 1 else 2*S
  have hrS : 2*S ≤ r := by dsimp [r]; split <;> omega
  have hr0 : 0 < r := by nlinarith
  have hrpar : (r + b) % 2 = 1 := by
    dsimp [r]
    split <;> omega
  let q : ℤ := r^3 + a*r^2 + b*r + c
  have hq : 0 < q := by exact hpos r hrS
  let d : ℤ := 3*r^2 + 2*a*r + b
  have hdodd : d % 2 = 1 := by
    have he := Int.even_mul_succ_self (r - 1)
    obtain ⟨t, ht⟩ := he
    have hmod : d ≡ r + b [ZMOD 2] := by
      rw [Int.modEq_iff_dvd]
      refine ⟨-t - r^2 - a*r, ?_⟩
      dsimp [d]
      nlinarith
    change d % 2 = (r + b) % 2 at hmod
    omega
  let N : ℤ := r + 2*q
  have hNS : 2*S ≤ N := by dsimp [N]; nlinarith
  have hN0 : 0 < N := by nlinarith
  let L : ℤ := 1 + 2*d + 4*q*(3*r + a) + 8*q^2
  have hpolyN : N^3 + a*N^2 + b*N + c = q * L := by
    dsimp [N, L, d, q]
    ring
  by_contra h
  push_neg at h
  obtain ⟨m, hm⟩ := h r hr0
  have hm2 : m^2 = q := by
    have hcastq : (q : ℝ) = (r : ℝ)^3 + a*r^2 + b*r + c := by
      dsimp [q]
      norm_num
    rw [← hcastq] at hm
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ q by exact_mod_cast hq.le)
    rw [hm] at hs
    exact_mod_cast hs
  obtain ⟨M, hM⟩ := h N hN0
  have hM2 : M^2 = q * L := by
    have hcastN : ((N^3 + a*N^2 + b*N + c : ℤ) : ℝ) =
        (N : ℝ)^3 + a*N^2 + b*N + c := by norm_num
    rw [← hcastN] at hM
    have hs := Real.sq_sqrt
      (show (0 : ℝ) ≤ ((N^3 + a*N^2 + b*N + c : ℤ) : ℝ) by
        exact_mod_cast (hpos N hNS).le)
    rw [hM] at hs
    have hsint : M^2 = N^3 + a*N^2 + b*N + c := by exact_mod_cast hs
    omega
  have hdvd : m^2 ∣ M^2 := by
    refine ⟨L, ?_⟩
    nlinarith
  have hmdvd : m ∣ M :=
    (IsIntegrallyClosed.pow_dvd_pow_iff (R := ℤ) (by norm_num : (2 : ℕ) ≠ 0)).mp hdvd
  obtain ⟨k, hk⟩ := hmdvd
  have hk2 : k^2 = L := by
    rw [hk] at hM2
    nlinarith
  have hLform : L = 1 + 2*d + 4*(q*(3*r+a) + 2*q^2) := by
    dsimp [L]
    ring
  have hLmod : L % 4 = 3 := by omega
  have hsquare (z : ℤ) : z^2 % 4 ≠ 3 := by
    have hz0 := Int.emod_nonneg z (by norm_num : (4 : ℤ) ≠ 0)
    have hz4 := Int.emod_lt_of_pos z (by norm_num : (0 : ℤ) < 4)
    intro hbad
    have hmul := Int.mul_emod z z 4
    have hcases : z % 4 = 0 ∨ z % 4 = 1 ∨ z % 4 = 2 ∨ z % 4 = 3 := by omega
    rw [pow_two] at hbad
    rcases hcases with hzr | hzr | hzr | hzr
    · norm_num [hzr] at hmul
      omega
    · norm_num [hzr] at hmul
      omega
    · norm_num [hzr] at hmul
      omega
    · norm_num [hzr] at hmul
      omega
  exact hsquare k (by omega)
