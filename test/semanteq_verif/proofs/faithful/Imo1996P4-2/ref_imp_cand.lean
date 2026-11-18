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
  rcases imo1996_p4_assumed.1 with ⟨a, b, m, n, ha, hb, hm, hn, habm, habn, hmin⟩
  have ha' : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha.le
  have hb' : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hb.le
  have hm' : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm.le
  have hn' : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn.le
  constructor
  · refine ⟨a.toNat, b.toNat, ?_, ?_, m.toNat, n.toNat, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · omega
    · apply Nat.cast_injective (R := ℤ)
      norm_num [ha', hb', hm']
      exact habm
    · have hba : 15 * b ≤ 16 * a := by nlinarith [habn, sq_nonneg n]
      have hba' : 15 * b.toNat ≤ 16 * a.toNat := by
        omega
      apply Nat.cast_injective (R := ℤ)
      rw [Nat.cast_sub hba']
      norm_num [ha', hb', hn']
      exact habn
    · have hmin' : min (m ^ 2) (n ^ 2) = 231361 := by
        simpa [solution] using hmin.symm
      apply Nat.cast_injective (R := ℤ)
      norm_num [hm', hn']
      exact hmin'
  · intro A B hA hB
    let X := Nat.sqrt (15 * A + 16 * B)
    let Y := Nat.sqrt (16 * A - 15 * B)
    refine ⟨X, Y, ?_⟩
    rintro ⟨hx, hy, h₁, h₂⟩
    have hYsq : 0 < Y ^ 2 := by positivity
    have hBA : 15 * B ≤ 16 * A := by omega
    have hmem : (min ((X : ℤ)^2) ((Y : ℤ)^2) : ℤ) ∈ S := by
      refine ⟨A, B, X, Y, by exact_mod_cast hA, by exact_mod_cast hB,
        by exact_mod_cast hx, by exact_mod_cast hy, ?_, ?_, rfl⟩
      · exact_mod_cast h₁
      · have h₂' := congrArg (fun k : ℕ => (k : ℤ)) h₂
        change ((16 * A - 15 * B : ℕ) : ℤ) = ((Y ^ 2 : ℕ) : ℤ) at h₂'
        rw [Nat.cast_sub hBA] at h₂'
        norm_num at h₂' ⊢
        exact h₂'
    have hle := imo1996_p4_assumed.2 _ hmem
    change (231361 : ℤ) ≤ min ((X : ℤ)^2) ((Y : ℤ)^2) at hle
    exact_mod_cast hle
