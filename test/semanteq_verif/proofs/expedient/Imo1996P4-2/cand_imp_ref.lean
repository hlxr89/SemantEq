import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev solution : ℤ := 231361

def S := { l | ∃ a b m n : ℤ,
    0 < a ∧ 0 < b ∧ 0 < m ∧ 0 < n ∧
    15*a + 16*b = m^2 ∧
    16*a - 15*b = n^2 ∧
    l = min (m^2) (n^2) }

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed : 
  (∃ (a b : ℕ), a > 0 ∧ b > 0 ∧ 
   ∃ (x y : ℕ), x > 0 ∧ y > 0 ∧ 
   15 * a + 16 * b = x^2 ∧ 
   16 * a - 15 * b = y^2 ∧
   min (x^2) (y^2) = 231361) ∧
  (∀ (a b : ℕ), a > 0 → b > 0 → 
   ∃ (x y : ℕ), x > 0 ∧ y > 0 ∧ 
   15 * a + 16 * b = x^2 ∧ 
   16 * a - 15 * b = y^2 →
   min (x^2) (y^2) ≥ 231361) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1996_p4 : solution ∈ S ∧ ∀ x ∈ S, solution ≤ x := by
  constructor
  · rcases problem_statement_assumed.1 with
      ⟨a, b, ha, hb, m, n, hm, hn, habm, habn, hmin⟩
    refine ⟨a, b, m, n, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact_mod_cast ha
    · exact_mod_cast hb
    · exact_mod_cast hm
    · exact_mod_cast hn
    · exact_mod_cast habm
    · have hn2 : 0 < n^2 := pow_pos hn 2
      have hle : 15 * b ≤ 16 * a := by omega
      exact_mod_cast habn
    · change (231361 : ℤ) = min ((m : ℤ)^2) ((n : ℤ)^2)
      exact_mod_cast hmin.symm
  · intro x hx
    rcases hx with ⟨a, b, m, n, ha, hb, hm, hn, habm, habn, rfl⟩
    have haeq : 15 * m^2 + 16 * n^2 = 481 * a := by nlinarith
    have hbeq : 16 * m^2 - 15 * n^2 = 481 * b := by nlinarith
    have div13 : ∀ u v : ℤ, 0 ≤ u → u < 13 → 0 ≤ v → v < 13 →
        15 * u^2 + 16 * v^2 ≡ 0 [ZMOD 13] → u = 0 ∧ v = 0 := by
      intro u v hu0 hu13 hv0 hv13 h
      interval_cases u <;> interval_cases v <;>
        norm_num [Int.ModEq, Int.modEq_iff_dvd] at h
      all_goals simp
    have div37 : ∀ u v : ℤ, 0 ≤ u → u < 37 → 0 ≤ v → v < 37 →
        16 * u^2 - 15 * v^2 ≡ 0 [ZMOD 37] → u = 0 ∧ v = 0 := by
      intro u v hu0 hu37 hv0 hv37 h
      interval_cases u <;> interval_cases v <;>
        norm_num [Int.ModEq, Int.modEq_iff_dvd] at h
      all_goals simp
    have hm13mod : m % 13 = 0 ∧ n % 13 = 0 := by
      apply div13 (m % 13) (n % 13)
      · exact Int.emod_nonneg m (by norm_num)
      · exact Int.emod_lt_of_pos m (by norm_num)
      · exact Int.emod_nonneg n (by norm_num)
      · exact Int.emod_lt_of_pos n (by norm_num)
      · calc
          15 * (m % 13)^2 + 16 * (n % 13)^2 ≡ 15 * m^2 + 16 * n^2 [ZMOD 13] := by
            exact ((Int.ModEq.refl 15).mul ((Int.mod_modEq m 13).pow 2)).add
              ((Int.ModEq.refl 16).mul ((Int.mod_modEq n 13).pow 2))
          _ ≡ 0 [ZMOD 13] := by
            rw [Int.modEq_zero_iff_dvd, haeq]
            exact ⟨37 * a, by ring⟩
    have hm37mod : m % 37 = 0 ∧ n % 37 = 0 := by
      apply div37 (m % 37) (n % 37)
      · exact Int.emod_nonneg m (by norm_num)
      · exact Int.emod_lt_of_pos m (by norm_num)
      · exact Int.emod_nonneg n (by norm_num)
      · exact Int.emod_lt_of_pos n (by norm_num)
      · calc
          16 * (m % 37)^2 - 15 * (n % 37)^2 ≡ 16 * m^2 - 15 * n^2 [ZMOD 37] := by
            exact ((Int.ModEq.refl 16).mul ((Int.mod_modEq m 37).pow 2)).sub
              ((Int.ModEq.refl 15).mul ((Int.mod_modEq n 37).pow 2))
          _ ≡ 0 [ZMOD 37] := by
            rw [Int.modEq_zero_iff_dvd, hbeq]
            exact ⟨13 * b, by ring⟩
    have hm481 : 481 ∣ m := by
      have hm13 := (Int.dvd_iff_emod_eq_zero).2 hm13mod.1
      have hm37 := (Int.dvd_iff_emod_eq_zero).2 hm37mod.1
      rcases hm13 with ⟨p, hp⟩
      rcases hm37 with ⟨q, hq⟩
      omega
    have hn481 : 481 ∣ n := by
      have hn13 := (Int.dvd_iff_emod_eq_zero).2 hm13mod.2
      have hn37 := (Int.dvd_iff_emod_eq_zero).2 hm37mod.2
      rcases hn13 with ⟨p, hp⟩
      rcases hn37 with ⟨q, hq⟩
      omega
    rcases hm481 with ⟨p, hp⟩
    rcases hn481 with ⟨q, hq⟩
    have hmge : 481 ≤ m := by omega
    have hnge : 481 ≤ n := by omega
    simp only [solution]
    rw [le_min_iff]
    constructor <;> nlinarith
