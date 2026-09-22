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
  rw [← putnam_1965_b3_refs_assumed]
  apply Set.ncard_congr (fun t _ => ((t.1 : ℤ), (t.2.1 : ℤ), (t.2.2 : ℤ)))
  · rintro ⟨a, b, c⟩ ⟨ha, hab, hp, harea⟩
    simp only [Set.mem_setOf_eq, Prod.fst, Prod.snd]
    have hc : 0 < c := by nlinarith [hp]
    norm_num at hp ⊢
    constructor
    · exact_mod_cast ha
    constructor
    · exact_mod_cast hab
    constructor
    · exact_mod_cast hc
    constructor
    · exact_mod_cast hp
    · norm_num [div_eq_iff]
      have hareaQ : (a : ℚ) * b = 4 * (a + b + c) := by exact_mod_cast harea
      nlinarith
  · rintro ⟨a, b, c⟩ ⟨d, e, f⟩ _ _ h
    simp only [Prod.mk.injEq, Int.ofNat_inj] at h
    simp_all
  · rintro ⟨a, b, c⟩ ⟨ha, hab, hc, hp, harea⟩
    refine ⟨(a.toNat, b.toNat, c.toNat), ?_, ?_⟩
    · simp only [Set.mem_setOf_eq, Prod.fst, Prod.snd]
      have ha0 : 0 ≤ a := le_of_lt ha
      have hb0 : 0 ≤ b := le_trans ha0 hab
      have hc0 : 0 ≤ c := le_of_lt hc
      have ha_cast : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha0
      have hb_cast : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hb0
      have hc_cast : (c.toNat : ℤ) = c := Int.toNat_of_nonneg hc0
      norm_num [div_eq_iff] at harea
      have hareaZ : a * b = 4 * (a + b + c) := by
        calc
          a * b = 2 * (a + b + c) * 2 := by exact_mod_cast harea
          _ = 4 * (a + b + c) := by ring
      constructor
      · omega
      constructor
      · omega
      constructor
      · apply Nat.cast_injective (R := ℤ)
        push_cast
        simpa only [ha_cast, hb_cast, hc_cast] using hp
      · apply Nat.cast_injective (R := ℤ)
        push_cast
        simpa only [ha_cast, hb_cast, hc_cast] using hareaZ
    · simp only [Prod.mk.injEq, Int.toNat_of_nonneg (le_of_lt ha),
        Int.toNat_of_nonneg (le_trans (le_of_lt ha) hab),
        Int.toNat_of_nonneg (le_of_lt hc), and_self]
