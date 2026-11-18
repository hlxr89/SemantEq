import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev solution (p : ℕ) : ℕ := 2 + (Nat.choose (2 * p) p - 2) / p

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (p : ℕ) (hp_prime : Nat.Prime p) (hp_odd : Odd p) :
  let S := Finset.Icc 1 (2 * p)
  let all_p_subsets := Finset.filter (fun A => A.card = p) (Finset.powerset S)
  let valid_subsets := Finset.filter (fun A => A.sum id % p = 0) all_p_subsets
  valid_subsets.card = 2 + (Nat.choose (2 * p) p - 2) / p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1995_p6 (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    (((Finset.Icc 1 (2 * p)).powersetCard p).filter
      (fun A ↦ p ∣ ∑ x ∈ A, x)).card = solution p := by
  have hpow :
      (Finset.Icc 1 (2 * p)).powersetCard p =
        Finset.filter (fun A => A.card = p) (Finset.powerset (Finset.Icc 1 (2 * p))) := by
    ext A
    simp only [Finset.mem_powersetCard, Finset.mem_filter, Finset.mem_powerset]
  have h := problem_statement_assumed p hp hodd
  dsimp only at h
  rw [← hpow] at h
  simpa only [solution, Nat.dvd_iff_mod_eq_zero] using h
