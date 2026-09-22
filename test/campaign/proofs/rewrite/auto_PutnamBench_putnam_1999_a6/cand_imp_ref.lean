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
  have hrat : ∀ n : ℕ, 1 ≤ n → ∃ q : ℚ, a n = (q : ℝ) := by
    intro n
    induction n using Nat.strong_induction_on with -- non-rewrite step
    | h n ih =>
      intro hn
      rcases Nat.eq_or_lt_of_le hn with hEq | hn1
      · subst n
        refine ⟨1, ?_⟩
        exact_mod_cast ha1
      have hn2 : 2 ≤ n := (Nat.succ_le_iff).mpr hn1
      rcases Nat.eq_or_lt_of_le hn2 with hEq | hn2'
      · subst n
        refine ⟨2, ?_⟩
        exact_mod_cast ha2
      have hn3 : 3 ≤ n := (Nat.succ_le_iff).mpr hn2'
      rcases Nat.eq_or_lt_of_le hn3 with hEq | hn3'
      · subst n
        refine ⟨24, ?_⟩
        exact_mod_cast ha3
      have hn4 : 4 ≤ n := (Nat.succ_le_iff).mpr hn3'
      have hnpos : 0 < n := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 3) hn4
      have hl1 : 1 ≤ n - 1 := Nat.le_sub_of_add_le hn2
      have hl2 : 1 ≤ n - 2 := Nat.le_sub_of_add_le hn3
      have hl3 : 1 ≤ n - 3 := Nat.le_sub_of_add_le hn4
      have ht1 : n - 1 < n := Nat.sub_lt hnpos (Nat.zero_lt_succ 0)
      have ht2 : n - 2 < n := Nat.sub_lt hnpos (Nat.zero_lt_succ 1)
      have ht3 : n - 3 < n := Nat.sub_lt hnpos (Nat.zero_lt_succ 2)
      obtain ⟨q1, hq1⟩ := ih (n - 1) ht1 hl1
      obtain ⟨q2, hq2⟩ := ih (n - 2) ht2 hl2
      obtain ⟨q3, hq3⟩ := ih (n - 3) ht3 hl3
      have hq1' : a ((n : ℤ) - 1) = (q1 : ℝ) := by
        simpa only [Int.ofNat_sub hn] using hq1
      have hq2' : a ((n : ℤ) - 2) = (q2 : ℝ) := by
        simpa only [Int.ofNat_sub hn2] using hq2
      have hq3' : a ((n : ℤ) - 3) = (q3 : ℝ) := by
        simpa only [Int.ofNat_sub hn3] using hq3
      have hrec : a n =
          (6 * (a (n - 1))^2 * (a (n - 3)) - 8 * (a (n - 1)) * (a (n - 2))^2) /
            (a (n - 2) * a (n - 3)) := by
        exact hange4 n hn4
      refine ⟨(6 * q1^2 * q3 - 8 * q1 * q2^2) / (q2 * q3), ?_⟩
      rw [hrec, hq1', hq2', hq3']
      norm_cast
  let b : ℕ → ℚ := fun n => if hn : 1 ≤ n then Classical.choose (hrat n hn) else 0
  have hb_cast (n : ℕ) (hn : 1 ≤ n) : a n = (b n : ℝ) := by
    simp only [b, dif_pos hn]
    exact Classical.choose_spec (hrat n hn)
  have hb1 : b 1 = 1 := by
    apply (Rat.cast_injective : Function.Injective (fun q : ℚ => (q : ℝ)))
    exact_mod_cast (hb_cast 1 (Nat.le_refl 1)).symm.trans ha1
  have hb2 : b 2 = 2 := by
    apply (Rat.cast_injective : Function.Injective (fun q : ℚ => (q : ℝ)))
    exact_mod_cast (hb_cast 2 (Nat.le_succ 1)).symm.trans ha2
  have hb3 : b 3 = 24 := by
    apply (Rat.cast_injective : Function.Injective (fun q : ℚ => (q : ℝ)))
    exact_mod_cast (hb_cast 3 (Nat.le_trans (Nat.le_succ 1) (Nat.le_succ 2))).symm.trans ha3
  have hb : ∀ n : ℕ, 4 ≤ n →
      b n = (6 * (b (n - 1)) ^ 2 * b (n - 3) - 8 * b (n - 1) * (b (n - 2)) ^ 2) /
        (b (n - 2) * b (n - 3)) := by
    intro n hn4
    have hn3 : 3 ≤ n := Nat.le_trans (Nat.le_succ 3) hn4
    have hn2 : 2 ≤ n := Nat.le_trans (Nat.le_succ 2) hn3
    have hn1 : 1 ≤ n := Nat.le_trans (Nat.le_succ 1) hn2
    have hl1 : 1 ≤ n - 1 := Nat.le_sub_of_add_le hn2
    have hl2 : 1 ≤ n - 2 := Nat.le_sub_of_add_le hn3
    have hl3 : 1 ≤ n - 3 := Nat.le_sub_of_add_le hn4
    have hbc1 : a ((n : ℤ) - 1) = (b (n - 1) : ℝ) := by
      simpa only [Int.ofNat_sub hn1] using hb_cast (n - 1) hl1
    have hbc2 : a ((n : ℤ) - 2) = (b (n - 2) : ℝ) := by
      simpa only [Int.ofNat_sub hn2] using hb_cast (n - 2) hl2
    have hbc3 : a ((n : ℤ) - 3) = (b (n - 3) : ℝ) := by
      simpa only [Int.ofNat_sub hn3] using hb_cast (n - 3) hl3
    apply (Rat.cast_injective : Function.Injective (fun q : ℚ => (q : ℝ)))
    simp only [Rat.cast_div, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow]
    rw [← hb_cast n hn1, ← hbc1, ← hbc2, ← hbc3]
    exact hange4 n hn4
  intro n hn
  have hnNat : 1 ≤ n.toNat := by
    rw [← Int.toNat_one]
    exact Int.toNat_le_toNat hn
  obtain ⟨k, hk⟩ := putnam_1999_a6_assumed b hb1 hb2 hb3 hb n.toNat hnNat
  refine ⟨k, ?_⟩
  have hn_nonneg : 0 ≤ n := Int.le_trans (Int.natCast_nonneg 1) hn
  rw [← Int.toNat_of_nonneg hn_nonneg, hb_cast n.toNat hnNat]
  exact_mod_cast hk.trans (mul_comm (n.toNat : ℚ) k)
