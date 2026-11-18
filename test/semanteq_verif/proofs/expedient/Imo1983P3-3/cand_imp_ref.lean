import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (hab : Nat.gcd a b = 1) (hbc : Nat.gcd b c = 1) (hca : Nat.gcd c a = 1) :
  let N := 2 * a * b * c - a * b - b * c - c * a
  (∀ n : ℕ, N < n → ∃ x y z : ℕ, n = x * b * c + y * c * a + z * a * b) ∧
  (¬ ∃ x y z : ℕ, N = x * b * c + y * c * a + z * a * b) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1983_p3 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b) (hbc : Nat.Coprime b c) (hca : Nat.Coprime c a) :
    IsGreatest
      {n : ℤ | ¬∃ x y z : ℕ, n = x * (b * c) + y * (c * a) + z * (a * b)}
      (2 * a * b * c - a * b - b * c - c * a) := by
  have h := problem_statement_assumed a b c ha hb hc hab.gcd_eq_one hbc.gcd_eq_one hca.gcd_eq_one
  dsimp only at h
  have hNpos : 0 < 2 * a * b * c - a * b - b * c - c * a := by
    by_contra hnot
    have hz : 2 * a * b * c - a * b - b * c - c * a = 0 := Nat.eq_zero_of_not_pos hnot
    apply h.2
    refine ⟨0, 0, 0, ?_⟩
    simp [hz]
  have hcast :
      ((2 * a * b * c - a * b - b * c - c * a : ℕ) : ℤ) =
        2 * a * b * c - a * b - b * c - c * a := by
    have h₁ : a * b ≤ 2 * a * b * c := by omega
    have h₂ : b * c ≤ 2 * a * b * c - a * b := by omega
    have h₃ : c * a ≤ 2 * a * b * c - a * b - b * c := by omega
    rw [Nat.cast_sub h₃, Nat.cast_sub h₂, Nat.cast_sub h₁]
    push_cast
    ring
  constructor
  · rintro ⟨x, y, z, heq⟩
    apply h.2
    refine ⟨x, y, z, ?_⟩
    have hi := hcast.trans heq
    norm_num [Nat.mul_assoc] at hi ⊢
    exact_mod_cast hi
  · intro n hn
    by_contra hle
    have hlt : 2 * a * b * c - a * b - b * c - c * a < n := lt_of_not_ge hle
    have hn0 : 0 ≤ n := by
      have : (0 : ℤ) < 2 * a * b * c - a * b - b * c - c * a := by
        rw [← hcast]
        exact_mod_cast hNpos
      omega
    have hnatlt : 2 * a * b * c - a * b - b * c - c * a < n.toNat := by
      have hlt' : ((2 * a * b * c - a * b - b * c - c * a : ℕ) : ℤ) < n := by
        simpa [hcast] using hlt
      exact_mod_cast (show ((2 * a * b * c - a * b - b * c - c * a : ℕ) : ℤ) <
        (n.toNat : ℤ) by simpa [Int.toNat_of_nonneg hn0] using hlt')
    rcases h.1 n.toNat hnatlt with ⟨x, y, z, hrep⟩
    apply hn
    refine ⟨x, y, z, ?_⟩
    have hncast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn0
    calc
      n = (n.toNat : ℤ) := hncast.symm
      _ = x * (b * c) + y * (c * a) + z * (a * b) := by
        have hrep' : n.toNat = x * (b * c) + y * (c * a) + z * (a * b) := by
          simpa [Nat.mul_assoc] using hrep
        simpa using congrArg (fun k : ℕ => (k : ℤ)) hrep'
