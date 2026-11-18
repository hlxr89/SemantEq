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
  have mod13 : ∀ u v : ZMod 13, 16 * u^2 = 15 * v^2 → u = 0 ∧ v = 0 := by
    native_decide
  have mod37 : ∀ u v : ZMod 37, 16 * u^2 = 15 * v^2 → u = 0 ∧ v = 0 := by
    native_decide
  constructor
  · rcases problem_statement_assumed.1 with
      ⟨a, b, ha, hb, x, y, hx, hy, habx, haby, hmin⟩
    refine ⟨(a : ℤ), (b : ℤ), (x : ℤ), (y : ℤ), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact_mod_cast ha
    · exact_mod_cast hb
    · exact_mod_cast hx
    · exact_mod_cast hy
    · exact_mod_cast habx
    · have hle : 15 * b ≤ 16 * a := by
        have hpos : 0 < 16 * a - 15 * b := by
          rw [haby]
          positivity
        omega
      exact_mod_cast haby
    · change (231361 : ℤ) = min ((x : ℤ)^2) ((y : ℤ)^2)
      exact_mod_cast hmin.symm
  · intro l hl
    rcases hl with ⟨a, b, m, n, ha, hb, hm, hn, habm, habn, rfl⟩
    have hrel : 16 * m^2 - 15 * n^2 = 481 * b := by
      nlinarith
    have hd13 : (13 : ℤ) ∣ 16 * m^2 - 15 * n^2 := by
      refine ⟨37 * b, ?_⟩
      nlinarith
    have hd37 : (37 : ℤ) ∣ 16 * m^2 - 15 * n^2 := by
      refine ⟨13 * b, ?_⟩
      nlinarith
    have hz13 : ((16 * m^2 - 15 * n^2 : ℤ) : ZMod 13) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hd13
    have hz37 : ((16 * m^2 - 15 * n^2 : ℤ) : ZMod 37) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hd37
    have he13 : (16 : ZMod 13) * (m : ZMod 13)^2 = 15 * (n : ZMod 13)^2 := by
      push_cast at hz13
      linear_combination hz13
    have he37 : (16 : ZMod 37) * (m : ZMod 37)^2 = 15 * (n : ZMod 37)^2 := by
      push_cast at hz37
      linear_combination hz37
    have hm13 : (13 : ℤ) ∣ m :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (mod13 _ _ he13).1
    have hn13 : (13 : ℤ) ∣ n :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (mod13 _ _ he13).2
    have hm37 : (37 : ℤ) ∣ m :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (mod37 _ _ he37).1
    have hn37 : (37 : ℤ) ∣ n :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (mod37 _ _ he37).2
    rcases hm13 with ⟨km, hkm⟩
    rcases hm37 with ⟨lm, hlm⟩
    rcases hn13 with ⟨kn, hkn⟩
    rcases hn37 with ⟨ln, hln⟩
    have hm481 : 481 ≤ m := by omega
    have hn481 : 481 ≤ n := by omega
    have hm_sq : (231361 : ℤ) ≤ m^2 := by nlinarith
    have hn_sq : (231361 : ℤ) ≤ n^2 := by nlinarith
    exact le_min hm_sq hn_sq
