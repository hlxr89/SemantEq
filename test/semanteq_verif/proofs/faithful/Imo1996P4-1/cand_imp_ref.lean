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
    0 < a ∧ 0 < b ∧ 0 < x ∧ 0 < y ∧
    15 * a + 16 * b = x^2 ∧ 
    16 * a - 15 * b = y^2 ∧
    min (x^2) (y^2) = 231361) ∧
  (∀ (a b : ℕ) (x y : ℕ), 
    0 < a → 0 < b → 0 < x → 0 < y →
    15 * a + 16 * b = x^2 → 
    16 * a - 15 * b = y^2 →
    min (x^2) (y^2) ≥ 231361) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1996_p4 : solution ∈ S ∧ ∀ x ∈ S, solution ≤ x := by
  rcases problem_statement_assumed with ⟨hex, hleast⟩
  rcases hex with ⟨a, b, m, n, ha, hb, hm, hn, hab, hab', hl⟩
  have hsub : 15 * b ≤ 16 * a := by omega
  constructor
  · change ∃ a b m n : ℤ, _
    refine ⟨a, b, m, n, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact_mod_cast ha
    · exact_mod_cast hb
    · exact_mod_cast hm
    · exact_mod_cast hn
    · exact_mod_cast hab
    · exact_mod_cast hab'
    · simpa [solution] using congrArg (fun z : ℕ => (z : ℤ)) hl.symm
  · intro l hlmem
    change ∃ a b m n : ℤ, _ at hlmem
    rcases hlmem with ⟨a', b', m', n', ha', hb', hm', hn', habz, habz', rfl⟩
    have ha_cast : (a'.toNat : ℤ) = a' := Int.toNat_of_nonneg (le_of_lt ha')
    have hb_cast : (b'.toNat : ℤ) = b' := Int.toNat_of_nonneg (le_of_lt hb')
    have hm_cast : (m'.toNat : ℤ) = m' := Int.toNat_of_nonneg (le_of_lt hm')
    have hn_cast : (n'.toNat : ℤ) = n' := Int.toNat_of_nonneg (le_of_lt hn')
    have hsubz : 15 * b' ≤ 16 * a' := by
      nlinarith [sq_nonneg n']
    have hsubn : 15 * b'.toNat ≤ 16 * a'.toNat := by
      have hz : (15 * b'.toNat : ℤ) ≤ 16 * a'.toNat := by
        simpa [ha_cast, hb_cast] using hsubz
      exact_mod_cast hz
    have habn : 15 * a'.toNat + 16 * b'.toNat = m'.toNat ^ 2 := by
      apply Int.ofNat_inj.mp
      push_cast
      simpa [ha_cast, hb_cast, hm_cast] using habz
    have habn' : 16 * a'.toNat - 15 * b'.toNat = n'.toNat ^ 2 := by
      apply Int.ofNat_inj.mp
      push_cast [hsubn]
      simpa [ha_cast, hb_cast, hn_cast] using habz'
    have ha_nat : 0 < a'.toNat := by
      have hz : (0 : ℤ) < a'.toNat := by simpa [ha_cast] using ha'
      exact_mod_cast hz
    have hb_nat : 0 < b'.toNat := by
      have hz : (0 : ℤ) < b'.toNat := by simpa [hb_cast] using hb'
      exact_mod_cast hz
    have hm_nat : 0 < m'.toNat := by
      have hz : (0 : ℤ) < m'.toNat := by simpa [hm_cast] using hm'
      exact_mod_cast hz
    have hn_nat : 0 < n'.toNat := by
      have hz : (0 : ℤ) < n'.toNat := by simpa [hn_cast] using hn'
      exact_mod_cast hz
    have hnleast := hleast a'.toNat b'.toNat m'.toNat n'.toNat
      ha_nat hb_nat hm_nat hn_nat habn habn'
    have hz : (231361 : ℤ) ≤ ((min (m'.toNat ^ 2) (n'.toNat ^ 2) : ℕ) : ℤ) := by
      exact_mod_cast hnleast
    push_cast at hz
    simpa [solution, hm_cast, hn_cast] using hz
