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
  rcases imo1996_p4_assumed with ⟨⟨a, b, m, n, ha, hb, hm, hn, hab, hab', hl⟩, hleast⟩
  have ha' : (a.toNat : ℤ) = a := by omega
  have hb' : (b.toNat : ℤ) = b := by omega
  have hm' : (m.toNat : ℤ) = m := by omega
  have hn' : (n.toNat : ℤ) = n := by omega
  constructor
  · refine ⟨a.toNat, b.toNat, m.toNat, n.toNat, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · omega
    · apply Int.ofNat_inj.mp
      simpa [ha', hb', hm'] using hab
    · have hle : 15 * b ≤ 16 * a := by nlinarith [sq_nonneg n]
      have hle' : 15 * b.toNat ≤ 16 * a.toNat := by
        apply Int.ofNat_le.mp
        simpa [ha', hb'] using hle
      apply Int.ofNat_inj.mp
      rw [Nat.cast_sub hle']
      simpa [ha', hb', hn'] using hab'
    · apply Int.ofNat_inj.mp
      simpa [hm', hn'] using hl.symm
  · intro a' b' x y ha₀ hb₀ hx hy heq heq'
    have hpos : 0 < y ^ 2 := pow_pos hy 2
    have hle : 15 * b' ≤ 16 * a' := by omega
    have hz : (min (x ^ 2) (y ^ 2) : ℤ) ∈ S := by
      refine ⟨a', b', x, y, by exact_mod_cast ha₀, by exact_mod_cast hb₀,
        by exact_mod_cast hx, by exact_mod_cast hy, ?_, ?_, ?_⟩
      · exact_mod_cast heq
      · have hcast : ((16 * a' - 15 * b' : ℕ) : ℤ) = (y : ℤ) ^ 2 := by
          exact_mod_cast heq'
        rw [Nat.cast_sub hle] at hcast
        exact hcast
      · norm_cast
    apply Int.ofNat_le.mp
    simpa using hleast _ hz
