import Mathlib

open EuclideanGeometry Topology Filter Complex

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem putnam_1965_b3_refs_assumed
: {(a, b, c) : ℤ × ℤ × ℤ | a > 0 ∧ a ≤ b ∧ c > 0 ∧ a^2 + b^2 = c^2 ∧ a*b/(2 : ℚ) = 2*(a + b + c)}.ncard = 3 :=
  by
    sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1965_b3 :
    {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ t.1 ≤ t.2.1 ∧ t.1 ^ 2 + t.2.1 ^ 2 = t.2.2 ^ 2 ∧
      t.1 * t.2.1 = 4 * (t.1 + t.2.1 + t.2.2)}.ncard = 3 := by
  let S := {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ t.1 ≤ t.2.1 ∧
    t.1 ^ 2 + t.2.1 ^ 2 = t.2.2 ^ 2 ∧
    t.1 * t.2.1 = 4 * (t.1 + t.2.1 + t.2.2)}
  let T := {(a, b, c) : ℤ × ℤ × ℤ | a > 0 ∧ a ≤ b ∧ c > 0 ∧
    a^2 + b^2 = c^2 ∧ a*b/(2 : ℚ) = 2*(a + b + c)}
  have hcard : S.ncard = T.ncard := by
    apply Set.ncard_congr
      (fun t (_ : t ∈ S) => ((t.1 : ℤ), (t.2.1 : ℤ), (t.2.2 : ℤ)))
    · rintro ⟨a, b, c⟩ ⟨ha, hab, hpy, harea⟩
      have hc : 0 < c := by nlinarith
      change (0 : ℤ) < a ∧ (a : ℤ) ≤ b ∧ (0 : ℤ) < c ∧
        (a : ℤ)^2 + (b : ℤ)^2 = (c : ℤ)^2 ∧
        (a : ℚ) * b / 2 = 2 * (a + b + c)
      refine ⟨by exact_mod_cast ha, by exact_mod_cast hab, by exact_mod_cast hc,
        by exact_mod_cast hpy, ?_⟩
      have hareaZ : (a : ℤ) * b = 4 * ((a : ℤ) + b + c) := by
        exact_mod_cast harea
      have hareaQ : (a : ℚ) * b = 4 * (a + b + c) := by
        exact_mod_cast hareaZ
      rw [div_eq_iff (by norm_num : (2 : ℚ) ≠ 0)]
      nlinarith
    · rintro ⟨a, b, c⟩ ⟨d, e, f⟩ _ _ h
      norm_num at h ⊢
      exact h
    · rintro ⟨a, b, c⟩ ⟨ha, hab, hc, hpy, harea⟩
      obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le ha.le
      obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le (le_trans ha.le hab)
      obtain ⟨c, rfl⟩ := Int.eq_ofNat_of_zero_le hc.le
      refine ⟨(a, b, c), ?_, rfl⟩
      change 0 < a ∧ a ≤ b ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧
        a * b = 4 * (a + b + c)
      refine ⟨by exact_mod_cast ha, by exact_mod_cast hab, by exact_mod_cast hpy, ?_⟩
      norm_num at harea
      have hareaQ : (a : ℚ) * b = 4 * (a + b + c) := by
        calc
          (a : ℚ) * b = 2 * ((a : ℚ) * b / 2) := by ring
          _ = 2 * (2 * (a + b + c)) := by rw [harea]
          _ = 4 * (a + b + c) := by ring
      exact_mod_cast hareaQ
  change S.ncard = 3
  rw [hcard]
  exact putnam_1965_b3_refs_assumed
