import Mathlib

open Filter Topology Metric

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem putnam_1999_a6_assumed (a : ℕ → ℚ)
    (ha1 : a 1 = 1) (ha2 : a 2 = 2) (ha3 : a 3 = 24)
    (ha : ∀ n : ℕ, 4 ≤ n →
      a n = (6 * (a (n - 1)) ^ 2 * a (n - 3) - 8 * a (n - 1) * (a (n - 2)) ^ 2) /
        (a (n - 2) * a (n - 3))) :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℤ, a n = (n : ℚ) * k := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1999_a6_refs
(a : ℤ → ℝ)
(ha1 : a 1 = 1)
(ha2 : a 2 = 2)
(ha3 : a 3 = 24)
(hange4 : ∀ n : ℕ, n ≥ 4 → a n = (6 * (a (n - 1))^2 * (a (n - 3)) - 8 * (a (n - 1)) * (a (n - 2))^2)/(a (n - 2) * a (n - 3)))
: ∀ n, n ≥ 1 → (∃ k : ℤ, a n = k * n) := by
  let r : ℕ → ℚ := fun i => 2 ^ i * (2 ^ i - 1)
  let q : ℕ → ℚ := fun n => ∏ i ∈ Finset.Ico 1 n, r i
  have hr (i : ℕ) (hi : 1 ≤ i) : r i ≠ 0 := by
    apply mul_ne_zero (pow_ne_zero _ (by norm_num))
    exact sub_ne_zero.mpr (ne_of_gt (one_lt_pow₀ (by norm_num) (by omega)))
  have hq0 (n : ℕ) : q n ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i hi
    exact hr i (Finset.mem_Ico.mp hi).1
  have hqstep (n : ℕ) (hn : 2 ≤ n) : q n = q (n - 1) * r (n - 1) := by
    have he : n = (n - 1) + 1 := by omega
    conv_lhs => rw [he]
    exact Finset.prod_Ico_succ_top (by omega) r
  have hrstep (i : ℕ) : r (i + 2) = 6 * r (i + 1) - 8 * r i := by
    simp only [r, pow_succ]
    ring
  have hqrec (n : ℕ) (hn : 4 ≤ n) :
      q n = (6 * (q (n - 1)) ^ 2 * q (n - 3) -
        8 * q (n - 1) * (q (n - 2)) ^ 2) /
          (q (n - 2) * q (n - 3)) := by
    have e0 : q n = q (n - 1) * r (n - 1) := hqstep n (by omega)
    have e1 : q (n - 1) = q (n - 2) * r (n - 2) := by
      have h := hqstep (n - 1) (by omega)
      rw [show n - 1 - 1 = n - 2 by omega] at h
      exact h
    have e2 : q (n - 2) = q (n - 3) * r (n - 3) := by
      have h := hqstep (n - 2) (by omega)
      rw [show n - 2 - 1 = n - 3 by omega] at h
      exact h
    have he0 : n - 3 + 2 = n - 1 := by omega
    have he1 : n - 3 + 1 = n - 2 := by omega
    have hh := hrstep (n - 3)
    rw [he0, he1] at hh
    rw [e0, e1, e2]
    field_simp [hq0]
    rw [hh]
    ring
  have hq1 : q 1 = 1 := by norm_num [q]
  have hq2 : q 2 = 2 := by rw [hqstep 2 (by omega), hq1]; norm_num [r]
  have hq3 : q 3 = 24 := by rw [hqstep 3 (by omega), hq2]; norm_num [r]
  have Hq := putnam_1999_a6_assumed q hq1 hq2 hq3 hqrec
  have haq : ∀ n : ℕ, 1 ≤ n → a (n : ℤ) = (q n : ℝ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases h4 : 4 ≤ n
      · have hm1 := ih (n - 1) (by omega) (by omega)
        have hm2 := ih (n - 2) (by omega) (by omega)
        have hm3 := ih (n - 3) (by omega) (by omega)
        have hc := congrArg ((↑) : ℚ → ℝ) (hqrec n h4)
        rw [hange4 n h4]
        rw [show (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) by omega,
          show (n : ℤ) - 2 = ((n - 2 : ℕ) : ℤ) by omega,
          show (n : ℤ) - 3 = ((n - 3 : ℕ) : ℤ) by omega,
          hm1, hm2, hm3]
        push_cast at hc
        exact hc.symm
      · interval_cases n
        · simpa [hq1] using ha1
        · simpa [hq2] using ha2
        · simpa [hq3] using ha3
  intro z hz
  have hz0 : 0 ≤ z := by omega
  have hzt : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz0
  obtain ⟨k, hk⟩ := Hq z.toNat (by omega)
  refine ⟨k, ?_⟩
  have haz := haq z.toNat (by omega)
  rw [hzt] at haz
  have hkR : (q z.toNat : ℝ) = (z.toNat : ℝ) * (k : ℝ) := by exact_mod_cast hk
  have hzR : (z : ℝ) = (z.toNat : ℝ) := by exact_mod_cast hzt.symm
  rw [haz, hkR, hzR]
  ring
