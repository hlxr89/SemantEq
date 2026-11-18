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
  rcases imo1996_p4_assumed with ⟨hsol, hleast⟩
  rcases hsol with ⟨a, b, m, n, ha, hb, hm, hn, hab, hab', hvalue⟩
  have ha' : (a.toNat : ℤ) = a := Int.toNat_of_nonneg (le_of_lt ha)
  have hb' : (b.toNat : ℤ) = b := Int.toNat_of_nonneg (le_of_lt hb)
  have hm' : (m.toNat : ℤ) = m := Int.toNat_of_nonneg (le_of_lt hm)
  have hn' : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (le_of_lt hn)
  constructor
  · refine ⟨a.toNat, b.toNat, m.toNat, n.toNat, ?_⟩
    have hsub : 15 * b ≤ 16 * a := by
      have hn2 : 0 < n ^ 2 := pow_pos hn _
      omega
    rw [← ha'] at ha hab hab' hsub
    rw [← hb'] at hb hab hab' hsub
    rw [← hm'] at hm hab hvalue
    rw [← hn'] at hn hab' hvalue
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
    · have hsubNat : 15 * b.toNat ≤ 16 * a.toNat := by exact_mod_cast hsub
      apply Nat.cast_injective (R := ℤ)
      push_cast [hsubNat]
      exact hab'
    · change (231361 : ℤ) = min ((m.toNat : ℤ) ^ 2) ((n.toNat : ℤ) ^ 2) at hvalue
      apply Nat.cast_injective (R := ℤ)
      push_cast
      exact hvalue.symm
  · intro A B X Y hA hB hX hY hAB hAB'
    have hsub : 15 * B ≤ 16 * A := by
      have hY2 : 0 < Y ^ 2 := pow_pos hY _
      omega
    have hmem : (↑(min (X^2) (Y^2)) : ℤ) ∈ S := by
      refine ⟨(A : ℤ), (B : ℤ), (X : ℤ), (Y : ℤ), ?_⟩
      constructor
      · exact_mod_cast hA
      constructor
      · exact_mod_cast hB
      constructor
      · exact_mod_cast hX
      constructor
      · exact_mod_cast hY
      constructor
      · exact_mod_cast hAB
      constructor
      · exact_mod_cast hAB'
      · norm_num
    have h := hleast (↑(min (X^2) (Y^2)) : ℤ) hmem
    norm_num [solution] at h
    apply le_min
    · exact_mod_cast h.1
    · exact_mod_cast h.2
