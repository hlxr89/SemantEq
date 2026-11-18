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
  (∃ (a b : ℕ) (x y : ℕ), 
    a > 0 ∧ b > 0 ∧ 
    x > 0 ∧ y > 0 ∧
    15 * a + 16 * b = x^2 ∧ 
    16 * a - 15 * b = y^2 ∧
    min (x^2) (y^2) = 231361) ∧
  (∀ (a b : ℕ) (x y : ℕ), 
    a > 0 → b > 0 → 
    x > 0 → y > 0 →
    15 * a + 16 * b = x^2 → 
    16 * a - 15 * b = y^2 →
    min (x^2) (y^2) ≥ 231361) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1996_p4 : solution ∈ S ∧ ∀ x ∈ S, solution ≤ x := by
  rcases problem_statement_assumed with ⟨hex, hleast⟩
  rcases hex with ⟨a, b, m, n, ha, hb, hm, hn, hab, hab', hvalue⟩
  constructor
  · refine ⟨(a : ℤ), (b : ℤ), (m : ℤ), (n : ℤ), ?_⟩
    have hn2 : 0 < n ^ 2 := pow_pos hn _
    have hsub : 15 * b ≤ 16 * a := by omega
    constructor
    · exact_mod_cast ha
    constructor
    · exact_mod_cast hb
    constructor
    · exact_mod_cast hm
    constructor
    · exact_mod_cast hn
    constructor
    · exact_mod_cast hab
    constructor
    · exact_mod_cast hab'
    · norm_num [solution]
      exact_mod_cast hvalue.symm
  · intro l hl
    rcases hl with ⟨a, b, m, n, ha, hb, hm, hn, hab, hab', rfl⟩
    have ha' : (a.toNat : ℤ) = a := Int.toNat_of_nonneg (le_of_lt ha)
    have hb' : (b.toNat : ℤ) = b := Int.toNat_of_nonneg (le_of_lt hb)
    have hm' : (m.toNat : ℤ) = m := Int.toNat_of_nonneg (le_of_lt hm)
    have hn' : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (le_of_lt hn)
    have hsub : 15 * b ≤ 16 * a := by
      have hn2 : 0 < n ^ 2 := pow_pos hn _
      omega
    rw [← ha'] at ha hab hab' hsub
    rw [← hb'] at hb hab hab' hsub
    rw [← hm'] at hm hab
    rw [← hn'] at hn hab'
    have hA : a.toNat > 0 := by exact_mod_cast ha
    have hB : b.toNat > 0 := by exact_mod_cast hb
    have hM : m.toNat > 0 := by exact_mod_cast hm
    have hN : n.toNat > 0 := by exact_mod_cast hn
    have hAB : 15 * a.toNat + 16 * b.toNat = m.toNat ^ 2 := by
      exact_mod_cast hab
    have hAB' : 16 * a.toNat - 15 * b.toNat = n.toNat ^ 2 := by
      have hsubNat : 15 * b.toNat ≤ 16 * a.toNat := by exact_mod_cast hsub
      apply Nat.cast_injective (R := ℤ)
      push_cast [hsubNat]
      exact hab'
    have h := hleast a.toNat b.toNat m.toNat n.toNat hA hB hM hN hAB hAB'
    have hM2 : 231361 ≤ m.toNat ^ 2 := h.trans (min_le_left _ _)
    have hN2 : 231361 ≤ n.toNat ^ 2 := h.trans (min_le_right _ _)
    apply le_min
    · change (231361 : ℤ) ≤ m ^ 2
      rw [← hm']
      exact_mod_cast hM2
    · change (231361 : ℤ) ≤ n ^ 2
      rw [← hn']
      exact_mod_cast hN2
