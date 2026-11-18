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
  let S : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    ((Finset.filter (fun p : ℕ × ℕ => p.1 * (i.val + 1) + p.2 * (j.val + 1) = n)
      (Finset.product (Finset.range (n + 1)) (Finset.range (n + 1)))).card : ℤ)
  have hcount (i j : Fin n) : S i j =
      ∑' a : ℕ, ∑' b : ℕ,
        if a * (i.1 + 1) + b * (j.1 + 1) = (n : ℤ) then 1 else 0 := by
    change (↑(Finset.filter (fun p : ℕ × ℕ =>
      p.1 * (i.val + 1) + p.2 * (j.val + 1) = n)
      (Finset.product (Finset.range (n + 1)) (Finset.range (n + 1)))).card : ℤ) = _
    rw [tsum_eq_sum (s := Finset.range (n + 1))]
    · have hinner : (fun a : ℕ => ∑' b : ℕ,
          (if a * (i.1 + 1) + b * (j.1 + 1) = (n : ℤ) then 1 else 0 : ℤ)) =
          (fun a : ℕ => ∑ b ∈ Finset.range (n + 1),
          (if a * (i.1 + 1) + b * (j.1 + 1) = (n : ℤ) then 1 else 0 : ℤ)) := by
        funext a
        apply tsum_eq_sum
        intro b hb
        simp only [Finset.mem_range, not_lt] at hb
        split
        · rename_i hab
          have hj : (1 : ℤ) ≤ (j.1 : ℤ) + 1 := by omega -- non-rewrite step
          have hbnonneg : (0 : ℤ) ≤ b := by positivity
          have hble : (b : ℤ) ≤ b * ((j.1 : ℤ) + 1) :=
            le_mul_of_one_le_right hbnonneg hj
          have hafirst : (0 : ℤ) ≤ a * ((i.1 : ℤ) + 1) := by positivity
          exfalso
          omega -- non-rewrite step
        · rfl
      have hfinite : (∑ a ∈ Finset.range (n + 1), ∑' b : ℕ,
          (if a * (i.1 + 1) + b * (j.1 + 1) = (n : ℤ) then 1 else 0 : ℤ)) =
          ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1),
          (if a * (i.1 + 1) + b * (j.1 + 1) = (n : ℤ) then 1 else 0 : ℤ) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact congrFun hinner a
      have hcard : (↑(Finset.filter (fun p : ℕ × ℕ =>
          p.1 * (i.val + 1) + p.2 * (j.val + 1) = n)
          (Finset.product (Finset.range (n + 1)) (Finset.range (n + 1)))).card : ℤ) =
          ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1),
          if a * (i.1 + 1) + b * (j.1 + 1) = (n : ℤ) then 1 else 0 := by
        have heq (a b : ℕ) :
            ((a : ℤ) * ((i.1 : ℤ) + 1) + (b : ℤ) * ((j.1 : ℤ) + 1) = n) ↔
            a * (i.1 + 1) + b * (j.1 + 1) = n := by
          norm_cast
        simp_rw [heq]
        rw [← Finset.sum_product (Finset.range (n + 1)) (Finset.range (n + 1))
          (fun p : ℕ × ℕ =>
            (if p.1 * (i.1 + 1) + p.2 * (j.1 + 1) = n then 1 else 0 : ℤ))]
        rw [Finset.sum_boole]
        rfl
      exact hcard.trans hfinite.symm
    · intro a ha
      simp only [Finset.mem_range, not_lt] at ha
      have hz : (fun b : ℕ =>
          (if a * (i.1 + 1) + b * (j.1 + 1) = (n : ℤ) then 1 else 0 : ℤ)) = 0 := by
        funext b
        split
        · rename_i hab
          have hi : (1 : ℤ) ≤ (i.1 : ℤ) + 1 := by omega -- non-rewrite step
          have hanonneg : (0 : ℤ) ≤ a := by positivity
          have hale : (a : ℤ) ≤ a * ((i.1 : ℤ) + 1) :=
            le_mul_of_one_le_right hanonneg hi
          have hbsecond : (0 : ℤ) ≤ b * ((j.1 : ℤ) + 1) := by positivity
          exfalso
          omega -- non-rewrite step
        · rfl
      exact (tsum_congr (g := (0 : ℕ → ℤ)) (fun b => congrFun hz b)).trans tsum_zero
  have hdet : Matrix.det S = putnam_2023_b6_solution n :=
    putnam_2023_b6_assumed n S hn hcount
  have hceil : ⌈(n / 2 : ℚ)⌉₊ = (n + 1) / 2 := by
    change Int.toNat ⌈(n / 2 : ℚ)⌉ = (n + 1) / 2
    rw [show ⌈(n / 2 : ℚ)⌉ = -((-n) / (2 : ℤ)) from
      Rat.ceil_natCast_div_natCast n 2]
    omega -- non-rewrite step
  rw [show (fun i j =>
      ((Finset.filter (fun p : ℕ × ℕ => p.1 * (i.val + 1) + p.2 * (j.val + 1) = n)
        (Finset.product (Finset.range (n + 1)) (Finset.range (n + 1)))).card : ℤ)) = S from rfl]
  rw [hdet]
  unfold putnam_2023_b6_solution
  rw [hceil]
  have hc : 0 < (n + 1) / 2 := by omega -- non-rewrite step
  rw [show (n + 1) / 2 + 1 = ((n + 1) / 2 - 1) + 2 by omega, pow_add] -- non-rewrite step
  simp only [pow_two, neg_one_mul, neg_neg, mul_one]
