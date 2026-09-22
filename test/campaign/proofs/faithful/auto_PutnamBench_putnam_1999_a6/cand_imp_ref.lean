import Mathlib

open Filter Topology Metric

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem putnam_1999_a6_assumed (a : ℕ → ℚ)
    (ha1 : a 1 = 1) (ha2 : a 2 = 2) (ha3 : a 3 = 24)
    (ha : ∀ n : ℕ, 4 ≤ n →
      a n = (6 * (a (n - 1)) ^ 2 * a (n - 3) - 8 * a (n - 1) * (a (n - 2)) ^ 2) /
        (a (n - 2) * a (n - 3))) :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℤ, a n = (n : ℚ) * k := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1999_a6_refs
(a : ℤ → ℝ)
(ha1 : a 1 = 1)
(ha2 : a 2 = 2)
(ha3 : a 3 = 24)
(hange4 : ∀ n : ℕ, n ≥ 4 → a n = (6 * (a (n - 1))^2 * (a (n - 3)) - 8 * (a (n - 1)) * (a (n - 2))^2)/(a (n - 2) * a (n - 3)))
: ∀ n, n ≥ 1 → (∃ k : ℤ, a n = k * n) := by
  have hrat : ∀ n : ℕ, 1 ≤ n → ∃ q : ℚ, (q : ℝ) = a n := by
    intro n hn0
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn1 : n = 1
      · subst n
        exact ⟨1, by simpa using ha1.symm⟩
      by_cases hn2 : n = 2
      · subst n
        exact ⟨2, by simpa using ha2.symm⟩
      by_cases hn3 : n = 3
      · subst n
        exact ⟨24, by simpa using ha3.symm⟩
      by_cases hn4 : 4 ≤ n
      · obtain ⟨q1, hq1⟩ := ih (n - 1) (by omega) (by omega)
        obtain ⟨q2, hq2⟩ := ih (n - 2) (by omega) (by omega)
        obtain ⟨q3, hq3⟩ := ih (n - 3) (by omega) (by omega)
        refine ⟨(6 * q1^2 * q3 - 8 * q1 * q2^2) / (q2 * q3), ?_⟩
        have hs1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
        have hs2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
        have hs3 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := by omega
        rw [hange4 n hn4, ← hs1, ← hs2, ← hs3, ← hq1, ← hq2, ← hq3]
        norm_cast
      · omega
  let q : ℕ → ℚ := fun n => if hn : 1 ≤ n then Classical.choose (hrat n hn) else 0
  have hq (n : ℕ) (hn : 1 ≤ n) : (q n : ℝ) = a n := by
    simp only [q, dif_pos hn]
    exact Classical.choose_spec (hrat n hn)
  have hqrec : ∀ n : ℕ, 4 ≤ n →
      q n = (6 * (q (n - 1)) ^ 2 * q (n - 3) - 8 * q (n - 1) * (q (n - 2)) ^ 2) /
        (q (n - 2) * q (n - 3)) := by
    intro n hn
    apply Rat.cast_injective (α := ℝ)
    push_cast
    rw [hq n (by omega), hq (n - 1) (by omega), hq (n - 2) (by omega),
      hq (n - 3) (by omega)]
    have hs1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    have hs2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
    have hs3 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := by omega
    rw [hs1, hs2, hs3]
    exact hange4 n hn
  have hq1 : q 1 = 1 := by
    exact_mod_cast (hq 1 (by omega)).trans ha1
  have hq2 : q 2 = 2 := by
    exact_mod_cast (hq 2 (by omega)).trans ha2
  have hq3 : q 3 = 24 := by
    exact_mod_cast (hq 3 (by omega)).trans ha3
  have hdiv := putnam_1999_a6_assumed q hq1 hq2 hq3 hqrec
  intro n hn
  have hn0 : 0 ≤ n := le_trans (by norm_num) hn
  obtain ⟨k, hk⟩ := hdiv n.toNat (by omega)
  refine ⟨k, ?_⟩
  have hncast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn0
  have hk' : (q n.toNat : ℝ) = (n.toNat : ℝ) * k := by exact_mod_cast hk
  have hqa : (q n.toNat : ℝ) = a n :=
    (hq n.toNat (by omega)).trans (congrArg a hncast)
  rw [hqa] at hk'
  rw [show (n.toNat : ℝ) = (n : ℝ) by exact_mod_cast hncast] at hk'
  simpa [mul_comm] using hk'
