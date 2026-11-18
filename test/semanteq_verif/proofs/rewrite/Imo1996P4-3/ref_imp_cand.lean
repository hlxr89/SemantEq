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
  (∃ (a b x y : ℕ), 
    0 < a ∧ 0 < b ∧ 
    0 < x ∧ 0 < y ∧
    15 * a + 16 * b = x^2 ∧ 
    16 * a - 15 * b = y^2 ∧
    min (x^2) (y^2) = 231361) ∧
  (∀ (a b x y : ℕ), 
    0 < a ∧ 0 < b ∧ 
    0 < x ∧ 0 < y ∧
    15 * a + 16 * b = x^2 ∧ 
    16 * a - 15 * b = y^2 →
    min (x^2) (y^2) ≥ 231361) := by
  obtain ⟨⟨a, b, x, y, ha, hb, hx, hy, habx, haby, hmin⟩, hleast⟩ :=
    imo1996_p4_assumed
  have ha' : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha.le
  have hb' : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hb.le
  have hx' : (x.toNat : ℤ) = x := Int.toNat_of_nonneg hx.le
  have hy' : (y.toNat : ℤ) = y := Int.toNat_of_nonneg hy.le
  have haN : 0 < a.toNat := Int.natCast_pos.mp (ha' ▸ ha)
  have hbN : 0 < b.toNat := Int.natCast_pos.mp (hb' ▸ hb)
  have hxN : 0 < x.toNat := Int.natCast_pos.mp (hx' ▸ hx)
  have hyN : 0 < y.toNat := Int.natCast_pos.mp (hy' ▸ hy)
  constructor
  · refine ⟨a.toNat, b.toNat, x.toNat, y.toNat, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact haN
    · exact hbN
    · exact hxN
    · exact hyN
    · rw [← ha', ← hb', ← hx'] at habx
      exact_mod_cast habx
    · have hxy : 15 * b < 16 * a := sub_pos.mp (haby.symm ▸ pow_pos hy 2)
      have hle : 15 * b.toNat ≤ 16 * a.toNat := by
        rw [← hb', ← ha'] at hxy
        exact_mod_cast hxy.le
      apply (Nat.sub_eq_iff_eq_add hle).mpr
      rw [← ha', ← hb', ← hy'] at haby
      exact_mod_cast (sub_eq_iff_eq_add.mp haby)
    · rw [← hx', ← hy'] at hmin
      change (231361 : ℤ) = min ((x.toNat : ℤ)^2) ((y.toNat : ℤ)^2) at hmin
      exact_mod_cast hmin.symm
  · intro a b x y h
    rcases h with ⟨ha, hb, hx, hy, habx, haby⟩
    have hsubpos : 0 < 16 * a - 15 * b := by rw [haby]; exact pow_pos hy 2
    have hle : 15 * b ≤ 16 * a := (Nat.lt_of_sub_pos hsubpos).le
    have hmem : ((min (x^2) (y^2) : ℕ) : ℤ) ∈ S := by
      refine ⟨a, b, x, y, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact_mod_cast ha
      · exact_mod_cast hb
      · exact_mod_cast hx
      · exact_mod_cast hy
      · exact_mod_cast habx
      · change (((16 * a : ℕ) : ℤ) - ((15 * b : ℕ) : ℤ)) = ((y^2 : ℕ) : ℤ)
        rw [← Nat.cast_sub hle]
        exact congrArg (fun z : ℕ => (z : ℤ)) haby
      · exact_mod_cast rfl
    have hbound := hleast ((min (x^2) (y^2) : ℕ) : ℤ) hmem
    change (231361 : ℤ) ≤ ((min (x^2) (y^2) : ℕ) : ℤ) at hbound
    exact_mod_cast hbound
