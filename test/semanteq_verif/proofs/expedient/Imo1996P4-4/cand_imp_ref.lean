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
  rcases problem_statement_assumed with ⟨⟨a, b, m, n, ha, hb, hm, hn, hab, hab', hl⟩, hleast⟩
  constructor
  · refine ⟨a, b, m, n, by exact_mod_cast ha, by exact_mod_cast hb,
      by exact_mod_cast hm, by exact_mod_cast hn, ?_, ?_, ?_⟩
    · exact_mod_cast hab
    · have hle : 15 * b ≤ 16 * a := by omega
      have hcast : ((16 * a - 15 * b : ℕ) : ℤ) = (n : ℤ) ^ 2 := by
        exact_mod_cast hab'
      rw [Nat.cast_sub hle] at hcast
      exact hcast
    · change (231361 : ℤ) = min ((m : ℤ) ^ 2) ((n : ℤ) ^ 2)
      exact_mod_cast hl.symm
  · rintro l ⟨a, b, m, n, ha, hb, hm, hn, hab, hab', rfl⟩
    have ha' : (a.toNat : ℤ) = a := by omega
    have hb' : (b.toNat : ℤ) = b := by omega
    have hm' : (m.toNat : ℤ) = m := by omega
    have hn' : (n.toNat : ℤ) = n := by omega
    have heq : 15 * a.toNat + 16 * b.toNat = m.toNat ^ 2 := by
      apply Int.ofNat_inj.mp
      simpa [ha', hb', hm'] using hab
    have hle : 15 * b ≤ 16 * a := by nlinarith [sq_nonneg n]
    have hle' : 15 * b.toNat ≤ 16 * a.toNat := by
      apply Int.ofNat_le.mp
      simpa [ha', hb'] using hle
    have heq' : 16 * a.toNat - 15 * b.toNat = n.toNat ^ 2 := by
      rw [← Nat.cast_inj (R := ℤ), Nat.cast_sub hle']
      norm_num [ha', hb', hn', hab']
    have h := hleast a.toNat b.toNat m.toNat n.toNat (by omega) (by omega)
      (by omega) (by omega) heq heq'
    have hcast : (231361 : ℤ) ≤ (min (m.toNat ^ 2) (n.toNat ^ 2) : ℕ) := by
      exact_mod_cast h
    simpa [hm', hn'] using hcast
