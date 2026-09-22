import Mathlib

open EuclideanGeometry Topology Filter Complex

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem putnam_1965_b3_assumed :
    {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ t.1 ≤ t.2.1 ∧ t.1 ^ 2 + t.2.1 ^ 2 = t.2.2 ^ 2 ∧
      t.1 * t.2.1 = 4 * (t.1 + t.2.1 + t.2.2)}.ncard = 3 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1965_b3_refs
: {(a, b, c) : ℤ × ℤ × ℤ | a > 0 ∧ a ≤ b ∧ c > 0 ∧ a^2 + b^2 = c^2 ∧ a*b/(2 : ℚ) = 2*(a + b + c)}.ncard = 3 := by
  calc
    _ = {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ t.1 ≤ t.2.1 ∧ t.1 ^ 2 + t.2.1 ^ 2 = t.2.2 ^ 2 ∧
      t.1 * t.2.1 = 4 * (t.1 + t.2.1 + t.2.2)}.ncard := by
      apply Set.ncard_congr
        (fun t _ => (t.1.toNat, t.2.1.toNat, t.2.2.toNat))
      · rintro ⟨a, b, c⟩ ⟨ha, hab, hc, hpyth, harea⟩
        have hna : 0 ≤ a := le_of_lt ha
        have hnb : 0 ≤ b := le_trans hna hab
        have hnc : 0 ≤ c := le_of_lt hc
        simp only [Set.mem_setOf_eq]
        have harea' : a * b = 4 * (a + b + c) := by
          norm_num [div_eq_iff] at harea
          ring_nf at harea ⊢
          exact_mod_cast harea
        constructor
        · omega
        constructor
        · omega
        constructor
        · rw [← Int.ofNat_inj]
          simp only [Nat.cast_add, Nat.cast_pow, Int.toNat_of_nonneg hna,
            Int.toNat_of_nonneg hnb, Int.toNat_of_nonneg hnc]
          exact hpyth
        · rw [← Int.ofNat_inj]
          simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add,
            Int.toNat_of_nonneg hna, Int.toNat_of_nonneg hnb,
            Int.toNat_of_nonneg hnc]
          exact harea'
      · rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ ha ha' heq
        have hna : 0 ≤ a := le_of_lt ha.1
        have hnb : 0 ≤ b := le_trans hna ha.2.1
        have hnc : 0 ≤ c := le_of_lt ha.2.2.1
        have hna' : 0 ≤ a' := le_of_lt ha'.1
        have hnb' : 0 ≤ b' := le_trans hna' ha'.2.1
        have hnc' : 0 ≤ c' := le_of_lt ha'.2.2.1
        simp only [Prod.mk.injEq] at heq ⊢
        rcases heq with ⟨haeq, hbeq, hceq⟩
        constructor
        · have h := congrArg (fun n : ℕ => (n : ℤ)) haeq
          simpa only [Int.toNat_of_nonneg hna, Int.toNat_of_nonneg hna'] using h
        constructor
        · have h := congrArg (fun n : ℕ => (n : ℤ)) hbeq
          simpa only [Int.toNat_of_nonneg hnb, Int.toNat_of_nonneg hnb'] using h
        · have h := congrArg (fun n : ℕ => (n : ℤ)) hceq
          simpa only [Int.toNat_of_nonneg hnc, Int.toNat_of_nonneg hnc'] using h
      · rintro ⟨a, b, c⟩ ⟨ha, hab, hpyth, harea⟩
        have hc : 0 < c := by
          nlinarith
        refine ⟨((a : ℤ), (b : ℤ), (c : ℤ)), ?_, ?_⟩
        · simp only [Set.mem_setOf_eq]
          constructor
          · exact_mod_cast ha
          constructor
          · exact_mod_cast hab
          constructor
          · exact_mod_cast hc
          constructor
          · exact_mod_cast hpyth
          · norm_num [div_eq_iff]
            have harea' : (a : ℤ) * (b : ℤ) = 4 * ((a : ℤ) + (b : ℤ) + (c : ℤ)) := by
              exact_mod_cast harea
            ring_nf at harea' ⊢
            exact_mod_cast harea'
        · simp
    _ = 3 := putnam_1965_b3_assumed
