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
  rcases imo1996_p4_assumed with ⟨hex, hmin⟩
  constructor
  · rcases hex with ⟨a, b, x, y, ha, hb, hx, hy, hab, hsub, hsol⟩
    have ea : (a.toNat : ℤ) = a := by omega
    have eb : (b.toNat : ℤ) = b := by omega
    have ex : (x.toNat : ℤ) = x := by omega
    have ey : (y.toNat : ℤ) = y := by omega
    refine ⟨a.toNat, b.toNat, x.toNat, y.toNat, ?_⟩
    have hsub' : 15 * b.toNat ≤ 16 * a.toNat := by
      apply Int.ofNat_le.mp
      push_cast
      rw [ea, eb]
      nlinarith [sq_nonneg y]
    constructor
    · omega
    constructor
    · omega
    constructor
    · omega
    constructor
    · omega
    constructor
    · apply Int.ofNat_inj.mp
      push_cast
      rw [ea, eb, ex]
      exact hab
    constructor
    · rw [Nat.sub_eq_iff_eq_add hsub']
      apply Int.ofNat_inj.mp
      push_cast
      rw [ea, eb, ey]
      nlinarith [hsub]
    · have hm : min (x ^ 2) (y ^ 2) = (231361 : ℤ) := by
        simpa [solution] using hsol.symm
      apply Int.ofNat_inj.mp
      push_cast
      rw [ex, ey]
      exact hm
  · intro a b x y ha hb hx hy hab hsub
    have hle : 15 * b ≤ 16 * a := by
      by_contra hn
      have hz : 16 * a - 15 * b = 0 := Nat.sub_eq_zero_of_le (by omega)
      rw [hz] at hsub
      nlinarith
    have hzsub : (16 : ℤ) * a - 15 * b = (y : ℤ) ^ 2 := by
      rw [sub_eq_iff_eq_add]
      exact_mod_cast (show 16 * a = y ^ 2 + 15 * b by
        omega)
    have hmem : ((min (x ^ 2) (y ^ 2) : ℕ) : ℤ) ∈ S := by
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
      · simpa using hzsub
      · simp
    have hz := hmin _ hmem
    change (231361 : ℤ) ≤ ((min (x ^ 2) (y ^ 2) : ℕ) : ℤ) at hz
    exact_mod_cast hz
