import Mathlib

open Filter Topology Metric

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem putnam_1999_a6_refs_assumed
(a : ℤ → ℝ)
(ha1 : a 1 = 1)
(ha2 : a 2 = 2)
(ha3 : a 3 = 24)
(hange4 : ∀ n : ℕ, n ≥ 4 → a n = (6 * (a (n - 1))^2 * (a (n - 3)) - 8 * (a (n - 1)) * (a (n - 2))^2)/(a (n - 2) * a (n - 3)))
: ∀ n, n ≥ 1 → (∃ k : ℤ, a n = k * n) :=
by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1999_a6 (a : ℕ → ℚ)
    (ha1 : a 1 = 1) (ha2 : a 2 = 2) (ha3 : a 3 = 24)
    (ha : ∀ n : ℕ, 4 ≤ n →
      a n = (6 * (a (n - 1)) ^ 2 * a (n - 3) - 8 * a (n - 1) * (a (n - 2)) ^ 2) /
        (a (n - 2) * a (n - 3))) :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℤ, a n = (n : ℚ) * k := by
  let b : ℤ → ℝ := fun z => (a z.toNat : ℝ)
  have hb1 : b 1 = 1 := by
    simpa only [b, Int.toNat_one, Rat.cast_one] using
      congrArg (fun q : ℚ => (q : ℝ)) ha1
  have hb2 : b 2 = 2 := by
    simpa only [b, Int.toNat_natCast, Rat.cast_ofNat] using
      congrArg (fun q : ℚ => (q : ℝ)) ha2
  have hb3 : b 3 = 24 := by
    simpa only [b, Int.toNat_natCast, Rat.cast_ofNat] using
      congrArg (fun q : ℚ => (q : ℝ)) ha3
  have hb : ∀ n : ℕ, n ≥ 4 → b n =
      (6 * (b (n - 1))^2 * (b (n - 3)) - 8 * (b (n - 1)) * (b (n - 2))^2) /
        (b (n - 2) * b (n - 3)) := by
    intro n hn
    have h3 : 3 ≤ n := Nat.le_trans (Nat.le_succ 3) hn
    have h2 : 2 ≤ n := Nat.le_trans (Nat.le_succ 2) h3
    have h1 : 1 ≤ n := Nat.le_trans (Nat.le_succ 1) h2
    simp only [b, Int.subNatNat_of_le h1, Int.subNatNat_of_le h2,
      Int.subNatNat_of_le h3, Int.toNat_natCast]
    exact_mod_cast ha n hn
  intro n hn
  obtain ⟨k, hk⟩ := putnam_1999_a6_refs_assumed b hb1 hb2 hb3 hb n (by exact_mod_cast hn)
  refine ⟨k, ?_⟩
  apply (Rat.cast_injective : Function.Injective (fun q : ℚ => (q : ℝ)))
  simpa only [b, Int.toNat_natCast, Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast,
    mul_comm] using hk
