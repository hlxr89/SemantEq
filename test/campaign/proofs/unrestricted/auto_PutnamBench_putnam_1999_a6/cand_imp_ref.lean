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
  have hrat : ∀ n : ℕ, 1 ≤ n → ∃ r : ℚ, (r : ℝ) = a n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases h1 : n = 1
      · subst n
        exact ⟨1, by norm_num [ha1]⟩
      by_cases h2 : n = 2
      · subst n
        exact ⟨2, by norm_num [ha2]⟩
      by_cases h3 : n = 3
      · subst n
        exact ⟨24, by norm_num [ha3]⟩
      have hn4 : 4 ≤ n := by omega
      obtain ⟨r1, hr1⟩ := ih (n - 1) (by omega) (by omega)
      obtain ⟨r2, hr2⟩ := ih (n - 2) (by omega) (by omega)
      obtain ⟨r3, hr3⟩ := ih (n - 3) (by omega) (by omega)
      refine ⟨(6 * r1^2 * r3 - 8 * r1 * r2^2) / (r2 * r3), ?_⟩
      rw [hange4 n hn4]
      have hm1 : ((n : ℤ) - 1) = (n - 1 : ℕ) := by omega
      have hm2 : ((n : ℤ) - 2) = (n - 2 : ℕ) := by omega
      have hm3 : ((n : ℤ) - 3) = (n - 3 : ℕ) := by omega
      rw [hm1, hm2, hm3]
      norm_num [hr1, hr2, hr3]
  let q : ℕ → ℚ := fun n => if hn : 1 ≤ n then Classical.choose (hrat n hn) else 0
  have hq : ∀ n : ℕ, 1 ≤ n → (q n : ℝ) = a n := by
    intro n hn
    simp only [q, dif_pos hn]
    exact Classical.choose_spec (hrat n hn)
  have hq1 : q 1 = 1 := by
    exact_mod_cast (hq 1 (by omega)).trans ha1
  have hq2 : q 2 = 2 := by
    exact_mod_cast (hq 2 (by omega)).trans ha2
  have hq3 : q 3 = 24 := by
    exact_mod_cast (hq 3 (by omega)).trans ha3
  have hqrec : ∀ n : ℕ, 4 ≤ n →
      q n = (6 * (q (n - 1)) ^ 2 * q (n - 3) - 8 * q (n - 1) * (q (n - 2)) ^ 2) /
        (q (n - 2) * q (n - 3)) := by
    intro n hn
    have hre := hange4 n hn
    have hm1 : ((n : ℤ) - 1) = (n - 1 : ℕ) := by omega
    have hm2 : ((n : ℤ) - 2) = (n - 2 : ℕ) := by omega
    have hm3 : ((n : ℤ) - 3) = (n - 3 : ℕ) := by omega
    rw [hm1, hm2, hm3] at hre
    rw [← hq n (by omega), ← hq (n - 1) (by omega),
      ← hq (n - 2) (by omega), ← hq (n - 3) (by omega)] at hre
    exact_mod_cast hre
  intro n hn
  have hn0 : 0 ≤ n := by omega
  have hnt : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn0
  obtain ⟨k, hk⟩ := putnam_1999_a6_assumed q hq1 hq2 hq3 hqrec n.toNat (by omega)
  refine ⟨k, ?_⟩
  have hcast := hq n.toNat (by omega)
  rw [hnt] at hcast
  have hntR : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast hnt
  calc
    a n = (q n.toNat : ℝ) := hcast.symm
    _ = ((((n.toNat : ℕ) : ℚ) * (k : ℚ) : ℚ) : ℝ) := congrArg (fun x : ℚ => (x : ℝ)) hk
    _ = (k : ℝ) * (n : ℝ) := by norm_num [hntR, mul_comm]
