import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev solution (p : ℕ) : ℕ := 2 + (Nat.choose (2 * p) p - 2) / p

-- ===== assumed statement (antecedent) =====
theorem imo1995_p6_assumed (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    (((Finset.Icc 1 (2 * p)).powersetCard p).filter
      (fun A ↦ p ∣ ∑ x ∈ A, x)).card = solution p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (p : ℕ) (hp_prime : Nat.Prime p) (hp_odd : Odd p) :
  let S := Finset.Icc 1 (2 * p)
  let all_p_subsets := Finset.filter (fun A => A.card = p) (Finset.powerset S)
  let valid_subsets := Finset.filter (fun A => A.sum id % p = 0) all_p_subsets
  valid_subsets.card = 2 + (Nat.choose (2 * p) p - 2) / p := by
  dsimp
  calc
    _ = (((Finset.Icc 1 (2 * p)).powersetCard p).filter
        (fun A ↦ p ∣ ∑ x ∈ A, x)).card := by
      congr 1
      ext A
      simp [Finset.mem_powersetCard, Nat.dvd_iff_mod_eq_zero]
    _ = solution p := imo1995_p6_assumed p hp_prime hp_odd
    _ = 2 + (Nat.choose (2 * p) p - 2) / p := rfl
