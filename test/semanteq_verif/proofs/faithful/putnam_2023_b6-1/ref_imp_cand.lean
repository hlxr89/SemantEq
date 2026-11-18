import Mathlib

open Nat Topology Filter

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_2023_b6_solution : ℕ → ℤ := (fun n : ℕ => (-1) ^ (⌈(n / 2 : ℚ)⌉₊ + 1) * 2 * ⌈(n / 2 : ℚ)⌉₊)

-- ===== assumed statement (antecedent) =====
theorem putnam_2023_b6_assumed
(n : ℕ)
(S : Matrix (Fin n) (Fin n) ℤ)
(npos : n > 0)
(hS : ∀ i j : Fin n, S i j = ∑' a : ℕ, ∑' b : ℕ, if a * (i.1 + 1) + b * (j.1 + 1) = (n : ℤ) then 1 else 0)
: S.det = putnam_2023_b6_solution n :=
by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (n : ℕ) (hn : 0 < n) :
  let s : ℕ → ℕ → ℕ := fun i j => 
    (Finset.filter (fun p : ℕ × ℕ => p.1 * i + p.2 * j = n) 
      (Finset.product (Finset.range (n + 1)) (Finset.range (n + 1)))).card
  let S : Matrix (Fin n) (Fin n) ℤ := fun i j => (s (i.val + 1) (j.val + 1) : ℤ)
  let ceiling_n_div_2 : ℕ := (n + 1) / 2
  Matrix.det S = (-1 : ℤ)^(ceiling_n_div_2 - 1) * 2 * (ceiling_n_div_2 : ℤ) := by
  dsimp only
  have hentry (i j : Fin n) :
      ((Finset.filter (fun p : ℕ × ℕ => p.1 * (i.val + 1) + p.2 * (j.val + 1) = n)
        (Finset.product (Finset.range (n + 1)) (Finset.range (n + 1)))).card : ℤ) =
        ∑' a : ℕ, ∑' b : ℕ,
          if a * (i.1 + 1) + b * (j.1 + 1) = (n : ℤ) then 1 else 0 := by
    have htsum :
        (∑' a : ℕ, ∑' b : ℕ,
          if a * (i.1 + 1) + b * (j.1 + 1) = (n : ℤ) then 1 else 0) =
        ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1),
          if a * (i.1 + 1) + b * (j.1 + 1) = (n : ℕ) then (1 : ℤ) else 0 := by
      rw [tsum_eq_sum (s := Finset.range (n + 1))]
      apply Finset.sum_congr rfl
      intro a ha
      rw [tsum_eq_sum (s := Finset.range (n + 1))]
      · apply Finset.sum_congr rfl
        intro b hb
        simp only [Finset.mem_range] at ha hb
        norm_cast
      · intro b hb
        simp only [Finset.mem_range, not_lt] at hb
        split_ifs with h
        · norm_cast at h
          have hj : 1 ≤ j.val + 1 := by omega
          have : n < b * (j.val + 1) := by nlinarith
          omega
        · rfl
      · intro a ha
        simp only [Finset.mem_range, not_lt] at ha
        rw [tsum_eq_sum (s := ∅)]
        · simp
        · intro b hb
          split_ifs with h
          · norm_cast at h
            have hi : 1 ≤ i.val + 1 := by omega
            have : n < a * (i.val + 1) := by nlinarith
            omega
          · rfl
    rw [htsum]
    calc
      ((Finset.filter (fun p : ℕ × ℕ => p.1 * (i.val + 1) + p.2 * (j.val + 1) = n)
        (Finset.product (Finset.range (n + 1)) (Finset.range (n + 1)))).card : ℤ) =
          ∑ p ∈ Finset.product (Finset.range (n + 1)) (Finset.range (n + 1)),
            if p.1 * (i.val + 1) + p.2 * (j.val + 1) = n then (1 : ℤ) else 0 := by
              apply Finset.natCast_card_filter
      _ = _ := by
        exact Finset.sum_product _ _ (fun p : ℕ × ℕ =>
          if p.1 * (i.val + 1) + p.2 * (j.val + 1) = n then (1 : ℤ) else 0)
  have href := putnam_2023_b6_assumed n
    (fun i j => ((Finset.filter (fun p : ℕ × ℕ => p.1 * (i.val + 1) + p.2 * (j.val + 1) = n)
      (Finset.product (Finset.range (n + 1)) (Finset.range (n + 1)))).card : ℤ)) hn hentry
  have hceil : ⌈(n / 2 : ℚ)⌉₊ = (n + 1) / 2 := by
    rw [← Int.ceil_toNat]
    change (⌈((n : ℚ) / (2 : ℕ))⌉ : ℤ).toNat = (n + 1) / 2
    rw [Rat.ceil_natCast_div_natCast]
    omega
  rw [href]
  simp only [putnam_2023_b6_solution, hceil]
  have hcpos : 0 < (n + 1) / 2 := by omega
  rw [show (n + 1) / 2 + 1 = ((n + 1) / 2 - 1) + 2 by omega, pow_add]
  norm_num
