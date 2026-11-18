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
  rcases problem_statement_assumed with ⟨⟨a, b, x, y, ha, hb, hx, hy, hab, hsub, hmin⟩, hleast⟩
  constructor
  · have hsub_pos : 0 < 16 * a - 15 * b := by
      rw [hsub]
      exact pow_pos hy 2
    have hba : 15 * b ≤ 16 * a := (Nat.sub_pos_iff_lt.mp hsub_pos).le
    refine ⟨a, b, x, y, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact_mod_cast ha -- non-rewrite step
    · exact_mod_cast hb -- non-rewrite step
    · exact_mod_cast hx -- non-rewrite step
    · exact_mod_cast hy -- non-rewrite step
    · exact_mod_cast hab -- non-rewrite step
    · have hsub_cast := congrArg (fun z : ℕ => (z : ℤ)) hsub
      change ((16 * a - 15 * b : ℕ) : ℤ) = ((y ^ 2 : ℕ) : ℤ) at hsub_cast
      rw [Int.ofNat_sub hba] at hsub_cast
      push_cast at hsub_cast
      exact hsub_cast
    · have hmin_cast := congrArg (fun z : ℕ => (z : ℤ)) hmin.symm
      push_cast at hmin_cast
      exact hmin_cast
  · intro l hl
    rcases hl with ⟨a, b, m, n, ha, hb, hm, hn, hab, hsub, hl⟩
    have ha' : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha.le
    have hb' : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hb.le
    have hm' : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm.le
    have hn' : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn.le
    have hsub_nonneg : 0 ≤ 16 * a - 15 * b := hsub.symm ▸ sq_nonneg n
    have hba : 15 * b ≤ 16 * a := sub_nonneg.mp hsub_nonneg
    have hba_nat : 15 * b.toNat ≤ 16 * a.toNat := by
      rw [← ha', ← hb'] at hba
      exact_mod_cast hba -- non-rewrite step
    have ha_nat : 0 < a.toNat := by
      exact_mod_cast (show (0 : ℤ) < (a.toNat : ℤ) by rw [ha']; exact ha) -- non-rewrite step
    have hb_nat : 0 < b.toNat := by
      exact_mod_cast (show (0 : ℤ) < (b.toNat : ℤ) by rw [hb']; exact hb) -- non-rewrite step
    have hm_nat : 0 < m.toNat := by
      exact_mod_cast (show (0 : ℤ) < (m.toNat : ℤ) by rw [hm']; exact hm) -- non-rewrite step
    have hn_nat : 0 < n.toNat := by
      exact_mod_cast (show (0 : ℤ) < (n.toNat : ℤ) by rw [hn']; exact hn) -- non-rewrite step
    have hleast' := hleast a.toNat b.toNat m.toNat n.toNat
      ha_nat hb_nat hm_nat hn_nat
    have hab_nat : 15 * a.toNat + 16 * b.toNat = m.toNat ^ 2 := by
      rw [← ha', ← hb', ← hm'] at hab
      exact_mod_cast hab -- non-rewrite step
    have hsub_nat : 16 * a.toNat - 15 * b.toNat = n.toNat ^ 2 := by
      apply Int.ofNat_injective
      change ((16 * a.toNat - 15 * b.toNat : ℕ) : ℤ) = ((n.toNat ^ 2 : ℕ) : ℤ)
      rw [Int.ofNat_sub hba_nat]
      push_cast
      rw [ha', hb', hn']
      exact hsub
    have hbound := hleast' hab_nat hsub_nat
    rw [hl]
    have hbound_cast : (231361 : ℤ) ≤ (min (m.toNat ^ 2) (n.toNat ^ 2) : ℕ) := by
      exact_mod_cast hbound -- non-rewrite step
    push_cast at hbound_cast
    rw [hm', hn'] at hbound_cast
    exact hbound_cast
