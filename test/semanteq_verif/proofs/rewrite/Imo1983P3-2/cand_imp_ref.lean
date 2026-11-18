import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (hab : Nat.gcd a b = 1) (hbc : Nat.gcd b c = 1) (hca : Nat.gcd c a = 1) :
  (¬ ∃ (x y z : ℕ), 2 * a * b * c - a * b - b * c - c * a = x * b * c + y * c * a + z * a * b) ∧
  (∀ n : ℕ, n > 2 * a * b * c - a * b - b * c - c * a → ∃ (x y z : ℕ), n = x * b * c + y * c * a + z * a * b) :=
by sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1983_p3 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b) (hbc : Nat.Coprime b c) (hca : Nat.Coprime c a) :
    IsGreatest
      {n : ℤ | ¬∃ x y z : ℕ, n = x * (b * c) + y * (c * a) + z * (a * b)}
      (2 * a * b * c - a * b - b * c - c * a) := by
  rcases problem_statement_assumed a b c ha hb hc hab hbc hca with ⟨hnot, hall⟩
  have htarget_ne : 2 * a * b * c - a * b - b * c - c * a ≠ 0 := by
    intro hzero
    apply hnot
    refine ⟨0, 0, 0, ?_⟩
    simp only [hzero, zero_mul, zero_add]
  have htarget_pos : 0 < 2 * a * b * c - a * b - b * c - c * a :=
    Nat.pos_of_ne_zero htarget_ne
  have hca_lt : c * a < 2 * a * b * c - a * b - b * c :=
    Nat.sub_pos_iff_lt.mp htarget_pos
  have hmid_pos : 0 < 2 * a * b * c - a * b - b * c :=
    lt_of_le_of_lt (Nat.zero_le (c * a)) hca_lt
  have hbc_lt : b * c < 2 * a * b * c - a * b :=
    Nat.sub_pos_iff_lt.mp hmid_pos
  have hfirst_pos : 0 < 2 * a * b * c - a * b :=
    lt_of_le_of_lt (Nat.zero_le (b * c)) hbc_lt
  have hab_lt : a * b < 2 * a * b * c :=
    Nat.sub_pos_iff_lt.mp hfirst_pos
  have hcast :
      ((2 * a * b * c - a * b - b * c - c * a : ℕ) : ℤ) =
        2 * a * b * c - a * b - b * c - c * a := by
    simp only [Nat.cast_sub (Nat.le_of_lt hca_lt), Nat.cast_sub (Nat.le_of_lt hbc_lt),
      Nat.cast_sub (Nat.le_of_lt hab_lt), Nat.cast_mul, Nat.cast_ofNat]
  constructor
  · intro hrep
    apply hnot
    rcases hrep with ⟨x, y, z, hxyz⟩
    refine ⟨x, y, z, ?_⟩
    apply Int.ofNat_inj.mp
    rw [hcast]
    simpa only [Nat.cast_add, Nat.cast_mul, mul_assoc] using hxyz
  · intro n hn
    by_cases hn0 : 0 ≤ n
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hn0
      rw [← hcast]
      have hnotlt : ¬(2 * a * b * c - a * b - b * c - c * a < n) := by
        intro hlt
        apply hn
        rcases hall n hlt with ⟨x, y, z, hxyz⟩
        refine ⟨x, y, z, ?_⟩
        simpa only [Nat.cast_add, Nat.cast_mul, mul_assoc] using
          congrArg (fun k : ℕ => (k : ℤ)) hxyz
      exact_mod_cast not_lt.mp hnotlt
    · have hnneg : n ≤ 0 := le_of_lt (lt_of_not_ge hn0)
      rw [← hcast]
      exact hnneg.trans (Int.natCast_nonneg _)
