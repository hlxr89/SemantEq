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
  rcases imo1996_p4_assumed with ⟨hex, hleast⟩
  constructor
  · rcases hex with ⟨a, b, x, y, ha, hb, hx, hy, habx, haby, hmin⟩
    have ha' : (a.toNat : ℤ) = a := Int.toNat_of_nonneg (le_of_lt ha)
    have hb' : (b.toNat : ℤ) = b := Int.toNat_of_nonneg (le_of_lt hb)
    have hx' : (x.toNat : ℤ) = x := Int.toNat_of_nonneg (le_of_lt hx)
    have hy' : (y.toNat : ℤ) = y := Int.toNat_of_nonneg (le_of_lt hy)
    have hsub : 15 * b.toNat ≤ 16 * a.toNat := by
      apply Int.ofNat_le.mp
      simp only [Nat.cast_mul, Nat.cast_ofNat, ha', hb']
      nlinarith [sq_nonneg y]
    refine ⟨a.toNat, b.toNat, x.toNat, y.toNat, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · omega
    · apply Int.ofNat_inj.mp
      simpa [ha', hb', hx'] using habx
    · apply Int.ofNat_inj.mp
      simpa [Nat.cast_sub hsub, ha', hb', hy'] using haby
    · apply Int.ofNat_inj.mp
      simpa [Nat.cast_min, hx', hy', solution] using hmin.symm
  · intro a b x y h
    rcases h with ⟨ha, hb, hx, hy, habx, haby⟩
    have hsub : 15 * b ≤ 16 * a := by
      have hy2 : 0 < y ^ 2 := by positivity
      omega
    have hmem : ((min (x ^ 2) (y ^ 2) : ℕ) : ℤ) ∈ S := by
      refine ⟨(a : ℤ), (b : ℤ), (x : ℤ), (y : ℤ), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact_mod_cast ha
      · exact_mod_cast hb
      · exact_mod_cast hx
      · exact_mod_cast hy
      · exact_mod_cast habx
      · simpa [Nat.cast_sub hsub] using congrArg (fun z : ℕ => (z : ℤ)) haby
      · simp [Nat.cast_min]
    have hleast' := hleast ((min (x ^ 2) (y ^ 2) : ℕ) : ℤ) hmem
    change (231361 : ℤ) ≤ (min (x ^ 2) (y ^ 2) : ℕ) at hleast'
    exact_mod_cast hleast'
