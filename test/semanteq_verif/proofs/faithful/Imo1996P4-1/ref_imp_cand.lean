import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev solution : ℤ := 231361

def S := { l | ∃ a b m n : ℤ,
    0 < a ∧ 0 < b ∧ 0 < m ∧ 0 < n ∧
    15*a + 16*b = m^2 ∧
    16*a - 15*b = n^2 ∧
    l = min (m^2) (n^2) }

-- ===== assumed statement (antecedent) =====
theorem imo1996_p4_assumed : solution ∈ S ∧ ∀ x ∈ S, solution ≤ x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement : 
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
  rcases imo1996_p4_assumed with ⟨hex, hleast⟩
  change (∃ a b m n : ℤ, _) at hex
  rcases hex with ⟨a, b, m, n, ha, hb, hm, hn, hab, hab', hl⟩
  have ha_cast : (a.toNat : ℤ) = a := Int.toNat_of_nonneg (le_of_lt ha)
  have hb_cast : (b.toNat : ℤ) = b := Int.toNat_of_nonneg (le_of_lt hb)
  have hm_cast : (m.toNat : ℤ) = m := Int.toNat_of_nonneg (le_of_lt hm)
  have hn_cast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (le_of_lt hn)
  have hsub : 15 * b ≤ 16 * a := by
    nlinarith [sq_nonneg n]
  have hsub_nat : 15 * b.toNat ≤ 16 * a.toNat := by
    have hz : (15 * b.toNat : ℤ) ≤ 16 * a.toNat := by
      simpa [ha_cast, hb_cast] using hsub
    exact_mod_cast hz
  have hab_nat : 15 * a.toNat + 16 * b.toNat = m.toNat ^ 2 := by
    apply Int.ofNat_inj.mp
    push_cast
    simpa [ha_cast, hb_cast, hm_cast] using hab
  have hab'_nat : 16 * a.toNat - 15 * b.toNat = n.toNat ^ 2 := by
    apply Int.ofNat_inj.mp
    push_cast [hsub_nat]
    simpa [ha_cast, hb_cast, hn_cast] using hab'
  have hmin_nat : min (m.toNat ^ 2) (n.toNat ^ 2) = 231361 := by
    apply Int.ofNat_inj.mp
    push_cast
    simpa [solution, hm_cast, hn_cast] using hl.symm
  have ha_nat : 0 < a.toNat := by
    have hz : (0 : ℤ) < a.toNat := by simpa [ha_cast] using ha
    exact_mod_cast hz
  have hb_nat : 0 < b.toNat := by
    have hz : (0 : ℤ) < b.toNat := by simpa [hb_cast] using hb
    exact_mod_cast hz
  have hm_nat : 0 < m.toNat := by
    have hz : (0 : ℤ) < m.toNat := by simpa [hm_cast] using hm
    exact_mod_cast hz
  have hn_nat : 0 < n.toNat := by
    have hz : (0 : ℤ) < n.toNat := by simpa [hn_cast] using hn
    exact_mod_cast hz
  constructor
  · exact ⟨a.toNat, b.toNat, m.toNat, n.toNat,
      ha_nat, hb_nat, hm_nat, hn_nat,
      hab_nat, hab'_nat, hmin_nat⟩
  · intro a' b' m' n' ha' hb' hm' hn' habn habn'
    have hn_sq : 0 < n' ^ 2 := pow_pos hn' 2
    have hsub' : 15 * b' ≤ 16 * a' := by omega
    have hmem : ((min (m' ^ 2) (n' ^ 2) : ℕ) : ℤ) ∈ S := by
      change ∃ a b m n : ℤ, _
      refine ⟨a', b', m', n', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact_mod_cast ha'
      · exact_mod_cast hb'
      · exact_mod_cast hm'
      · exact_mod_cast hn'
      · exact_mod_cast habn
      · exact_mod_cast habn'
      · simp
    have hz := hleast _ hmem
    have hz' : (231361 : ℤ) ≤ ((min (m' ^ 2) (n' ^ 2) : ℕ) : ℤ) := by
      simpa [solution] using hz
    exact_mod_cast hz'
