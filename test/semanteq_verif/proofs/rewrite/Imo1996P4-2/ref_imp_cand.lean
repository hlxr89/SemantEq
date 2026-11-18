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
  rcases imo1996_p4_assumed with ⟨hmem, hleast⟩
  change (231361 : ℤ) ∈ S at hmem
  rcases hmem with ⟨a, b, x, y, ha, hb, hx, hy, habx, haby, hmin⟩
  have ha_cast : (a.toNat : ℤ) = a := Int.toNat_of_nonneg (le_of_lt ha)
  have hb_cast : (b.toNat : ℤ) = b := Int.toNat_of_nonneg (le_of_lt hb)
  have hx_cast : (x.toNat : ℤ) = x := Int.toNat_of_nonneg (le_of_lt hx)
  have hy_cast : (y.toNat : ℤ) = y := Int.toNat_of_nonneg (le_of_lt hy)
  have hab_nonneg : 15 * b ≤ 16 * a :=
    sub_nonneg.mp (haby.symm ▸ sq_nonneg y)
  have hab_nonneg_nat : 15 * b.toNat ≤ 16 * a.toNat := by
    rw [← Int.ofNat_le]
    simpa only [Nat.cast_mul, Nat.cast_ofNat, ha_cast, hb_cast] using hab_nonneg
  constructor
  · refine ⟨a.toNat, b.toNat, ?_, ?_, x.toNat, y.toNat, ?_, ?_, ?_, ?_, ?_⟩
    · apply Int.natCast_pos.mp
      rw [ha_cast]
      exact ha
    · apply Int.natCast_pos.mp
      rw [hb_cast]
      exact hb
    · apply Int.natCast_pos.mp
      rw [hx_cast]
      exact hx
    · apply Int.natCast_pos.mp
      rw [hy_cast]
      exact hy
    · rw [← Nat.cast_inj (R := ℤ)]
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
        ha_cast, hb_cast, hx_cast] using habx
    · rw [← Nat.cast_inj (R := ℤ), Int.ofNat_sub hab_nonneg_nat]
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
        ha_cast, hb_cast, hy_cast] using haby
    · rw [← Nat.cast_inj (R := ℤ), Nat.cast_min]
      simpa only [Nat.cast_pow, Nat.cast_ofNat, hx_cast, hy_cast] using hmin.symm
  · intro a' b' ha' hb'
    refine ⟨1, 1, ?_⟩
    intro h
    rcases h with ⟨_, _, habx', haby'⟩
    have hab_nonneg_nat' : 15 * b' ≤ 16 * a' := by
      apply Nat.le_of_lt
      rw [← Nat.sub_pos_iff_lt, haby']
      exact Nat.zero_lt_one
    have hone : (231361 : ℤ) ≤ min ((1 : ℤ)^2) ((1 : ℤ)^2) := by
      apply hleast
      refine ⟨a', b', 1, 1, ?_⟩
      refine ⟨by exact_mod_cast ha', by exact_mod_cast hb', by simp only [Int.reduceLT],
        by simp only [Int.reduceLT], ?_, ?_, rfl⟩
      · exact_mod_cast habx'
      · have haby_cast := congrArg (fun z : ℕ => (z : ℤ)) haby'
        simpa only [Int.ofNat_sub hab_nonneg_nat', Nat.cast_mul, Nat.cast_ofNat,
          Nat.cast_pow] using haby_cast
    exact_mod_cast hone
