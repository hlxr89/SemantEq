import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a b c : ℤ} : ∃ (n : ℕ) (hn : 0 < n), ¬ ∃ (m : ℤ), n ^ 3 + a * n ^ 2 + b * n + c = m ^ 2 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1998_b6 (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  let k : ℤ := |a| + |b| + |c| + 1
  rcases (dummy_assumed
    (a := 3 * k + a)
    (b := 3 * k ^ 2 + 2 * a * k + b)
    (c := k ^ 3 + a * k ^ 2 + b * k + c)) with ⟨n, hn, hns⟩
  let N : ℤ := n + k
  have ha : -|a| ≤ a := neg_abs_le a
  have hb : -|b| ≤ b := neg_abs_le b
  have hc : -|c| ≤ c := neg_abs_le c
  have hk : 0 < k := by
    dsimp [k]
    have haa : 0 ≤ |a| := abs_nonneg a
    have hbb : 0 ≤ |b| := abs_nonneg b
    have hcc : 0 ≤ |c| := abs_nonneg c
    omega
  have hnz : (0 : ℤ) < n := by exact_mod_cast hn
  have hN : 0 < N := by
    dsimp [N]
    omega
  have hNk : k < N := by
    dsimp [N]
    omega
  have hpoly : 0 < N ^ 3 + a * N ^ 2 + b * N + c := by
    have hN1 : 1 ≤ N := by omega
    have hN2 : 0 ≤ N ^ 2 := sq_nonneg N
    have hka : |a| ≤ k - 1 := by
      dsimp [k]
      have hbb : 0 ≤ |b| := abs_nonneg b
      have hcc : 0 ≤ |c| := abs_nonneg c
      omega
    have hkb : |b| ≤ k - 1 := by
      dsimp [k]
      have haa : 0 ≤ |a| := abs_nonneg a
      have hcc : 0 ≤ |c| := abs_nonneg c
      omega
    have hkc : |c| ≤ k - 1 := by
      dsimp [k]
      have haa : 0 ≤ |a| := abs_nonneg a
      have hbb : 0 ≤ |b| := abs_nonneg b
      omega
    nlinarith
  refine ⟨N, hN, ?_⟩
  rintro ⟨m, hm⟩
  apply hns
  refine ⟨m, ?_⟩
  have hnonneg : (0 : ℝ) ≤
      (N : ℝ) ^ 3 + (a : ℝ) * (N : ℝ) ^ 2 + (b : ℝ) * (N : ℝ) + c := by
    exact_mod_cast (le_of_lt hpoly)
  have hsquareR : (N ^ 3 + a * N ^ 2 + b * N + c : ℝ) = (m : ℝ) ^ 2 := by
    calc
      (N ^ 3 + a * N ^ 2 + b * N + c : ℝ) =
          (Real.sqrt (N ^ 3 + a * N ^ 2 + b * N + c)) ^ 2 := by
            exact (Real.sq_sqrt hnonneg).symm
      _ = (m : ℝ) ^ 2 := by rw [hm]
  have hsquareZ : N ^ 3 + a * N ^ 2 + b * N + c = m ^ 2 := by
    exact_mod_cast hsquareR
  dsimp [N] at hsquareZ ⊢
  exact (by
    calc
      (n : ℤ) ^ 3 + (3 * k + a) * (n : ℤ) ^ 2 +
          (3 * k ^ 2 + 2 * a * k + b) * (n : ℤ) +
          (k ^ 3 + a * k ^ 2 + b * k + c) =
          ((n : ℤ) + k) ^ 3 + a * ((n : ℤ) + k) ^ 2 +
            b * ((n : ℤ) + k) + c := by ring
      _ = m ^ 2 := hsquareZ)
