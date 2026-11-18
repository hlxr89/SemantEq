import Mathlib

open Nat Topology Filter

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_2023_b6_solution : ℕ → ℤ := (fun n : ℕ => (-1) ^ (⌈(n / 2 : ℚ)⌉₊ + 1) * 2 * ⌈(n / 2 : ℚ)⌉₊)

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (n : ℕ) (hn : 0 < n) :
  let s : ℕ → ℕ → ℕ := fun i j => 
    (Finset.filter (fun p : ℕ × ℕ => p.1 * i + p.2 * j = n) 
      (Finset.product (Finset.range (n + 1)) (Finset.range (n + 1)))).card
  let S : Matrix (Fin n) (Fin n) ℤ := fun i j => (s (i.val + 1) (j.val + 1) : ℤ)
  let ceiling_n_div_2 : ℕ := (n + 1) / 2
  Matrix.det S = (-1 : ℤ)^(ceiling_n_div_2 - 1) * 2 * (ceiling_n_div_2 : ℤ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_2023_b6
(n : ℕ)
(S : Matrix (Fin n) (Fin n) ℤ)
(npos : n > 0)
(hS : ∀ i j : Fin n, S i j = ∑' a : ℕ, ∑' b : ℕ, if a * (i.1 + 1) + b * (j.1 + 1) = (n : ℤ) then 1 else 0)
: S.det = putnam_2023_b6_solution n :=
by
  classical
  have count_eq_tsum (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
      (∑' a : ℕ, ∑' b : ℕ,
        if a * i + b * j = (n : ℤ) then (1 : ℤ) else 0) =
        ((Finset.filter (fun p : ℕ × ℕ => p.1 * i + p.2 * j = n)
          (Finset.product (Finset.range (n + 1)) (Finset.range (n + 1)))).card : ℤ) := by
    rw [tsum_eq_sum (s := Finset.range (n + 1))]
    · have hinner : ∀ a : ℕ,
          (∑' b : ℕ, if a * i + b * j = (n : ℤ) then (1 : ℤ) else 0) =
          ∑ b ∈ Finset.range (n + 1),
            if a * i + b * j = (n : ℤ) then (1 : ℤ) else 0 := by
        intro a
        apply tsum_eq_sum
        intro b hb
        simp only [Finset.mem_range, not_lt] at hb
        have hbj : b ≤ b * j := Nat.le_mul_of_pos_right b hj
        have hne : (a * i + b * j : ℤ) ≠ (n : ℤ) := by
          norm_cast
          omega
        simp [hne]
      simp_rw [hinner]
      rw [← Finset.sum_boole]
      norm_cast
      exact (Finset.sum_product' (Finset.range (n + 1)) (Finset.range (n + 1))
        (fun a b => if a * i + b * j = n then 1 else 0)).symm
    · intro a ha
      simp only [Finset.mem_range, not_lt] at ha
      have hne : ∀ b : ℕ, (a * i + b * j : ℤ) ≠ (n : ℤ) := by
        intro b
        have hai : a ≤ a * i := Nat.le_mul_of_pos_right a hi
        norm_cast
        omega
      simp only [hne, ↓reduceIte, tsum_zero]
  have ceil_half : ⌈(n / 2 : ℚ)⌉₊ = (n + 1) / 2 := by
    apply (Nat.ceil_eq_iff (by omega : (n + 1) / 2 ≠ 0)).2
    constructor
    · rw [lt_div_iff₀ (by norm_num : (0 : ℚ) < 2)]
      norm_cast
      omega
    · rw [div_le_iff₀ (by norm_num : (0 : ℚ) < 2)]
      norm_cast
      omega
  let T : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    ((Finset.filter (fun p : ℕ × ℕ => p.1 * (i.val + 1) + p.2 * (j.val + 1) = n)
      (Finset.product (Finset.range (n + 1)) (Finset.range (n + 1)))).card : ℤ)
  have hST : S = T := by
    ext i j
    rw [hS]
    exact count_eq_tsum (i.1 + 1) (j.1 + 1) (by omega) (by omega)
  have hcand := problem_statement_assumed n npos
  dsimp only at hcand
  change Matrix.det T = (-1 : ℤ) ^ ((n + 1) / 2 - 1) * 2 * ((n + 1) / 2 : ℤ) at hcand
  rw [hST, hcand]
  unfold putnam_2023_b6_solution
  rw [ceil_half]
  have hc : 0 < (n + 1) / 2 := by omega
  have hexp : (n + 1) / 2 + 1 = ((n + 1) / 2 - 1) + 2 := by omega
  rw [hexp, pow_add]
  norm_num
