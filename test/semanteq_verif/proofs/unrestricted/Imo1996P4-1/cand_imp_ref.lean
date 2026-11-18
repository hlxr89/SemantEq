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
  rcases problem_statement_assumed with ⟨hex, hmin⟩
  constructor
  · rcases hex with ⟨a, b, x, y, ha, hb, hx, hy, hab, hsub, hm⟩
    have hle : 15 * b ≤ 16 * a := by
      by_contra hn
      have hz : 16 * a - 15 * b = 0 := Nat.sub_eq_zero_of_le (by omega)
      rw [hz] at hsub
      nlinarith
    refine ⟨a, b, x, y, ?_⟩
    constructor
    · exact_mod_cast ha
    constructor
    · exact_mod_cast hb
    constructor
    · exact_mod_cast hx
    constructor
    · exact_mod_cast hy
    constructor
    · exact_mod_cast hab
    constructor
    · rw [sub_eq_iff_eq_add]
      exact_mod_cast (show 16 * a = y ^ 2 + 15 * b by omega)
    · change (231361 : ℤ) = min ((x : ℤ) ^ 2) ((y : ℤ) ^ 2)
      exact_mod_cast hm.symm
  · intro l hl
    rcases hl with ⟨a, b, x, y, ha, hb, hx, hy, hab, hsub, rfl⟩
    have ea : (a.toNat : ℤ) = a := by omega
    have eb : (b.toNat : ℤ) = b := by omega
    have ex : (x.toNat : ℤ) = x := by omega
    have ey : (y.toNat : ℤ) = y := by omega
    have hnsub : 16 * a.toNat - 15 * b.toNat = y.toNat ^ 2 := by
      have hle : 15 * b.toNat ≤ 16 * a.toNat := by
        apply Int.ofNat_le.mp
        push_cast
        rw [ea, eb]
        nlinarith [sq_nonneg y]
      rw [Nat.sub_eq_iff_eq_add hle]
      apply Int.ofNat_inj.mp
      push_cast
      rw [ea, eb, ey]
      nlinarith [hsub]
    have hnab : 15 * a.toNat + 16 * b.toNat = x.toNat ^ 2 := by
      apply Int.ofNat_inj.mp
      push_cast
      rw [ea, eb, ex]
      exact hab
    have hn := hmin a.toNat b.toNat x.toNat y.toNat (by omega) (by omega)
      (by omega) (by omega) hnab hnsub
    have hz : (231361 : ℤ) ≤ min ((x.toNat : ℤ) ^ 2) ((y.toNat : ℤ) ^ 2) := by
      exact_mod_cast hn
    simpa [solution, ex, ey] using hz
