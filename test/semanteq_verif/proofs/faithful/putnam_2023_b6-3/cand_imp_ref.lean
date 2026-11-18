import Mathlib

open Nat Topology Filter

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_2023_b6_solution : ℕ → ℤ := (fun n : ℕ => (-1) ^ (⌈(n / 2 : ℚ)⌉₊ + 1) * 2 * ⌈(n / 2 : ℚ)⌉₊)

/-- For a given n, i, j, returns the number of pairs (a,b) of nonnegative integers
    satisfying a*i + b*j = n. -/
def s (n i j : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun p : ℕ × ℕ => p.1 * i + p.2 * j = n) 
    (Finset.product (Finset.range (n / i + 1)) (Finset.range (n / j + 1))))

/-- The n-by-n matrix S where the (i,j) entry is s(i,j) for i,j ∈ {1,2,...,n}. -/
def S (n : ℕ) : Matrix (Fin n) (Fin n) ℕ :=
  fun i j => s n (i.val + 1) (j.val + 1)

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (n : ℕ) (hn : 0 < n) :
  Matrix.det ((S n).map (Nat.cast : ℕ → ℤ)) = 
    ((-1 : ℤ) ^ ((n / 2 + (n % 2)) - 1) * 2 * (n / 2 + (n % 2))) :=
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_2023_b6
(n : ℕ)
(S : Matrix (Fin n) (Fin n) ℤ)
(npos : n > 0)
(hS : ∀ i j : Fin n, S i j = ∑' a : ℕ, ∑' b : ℕ, if a * (i.1 + 1) + b * (j.1 + 1) = (n : ℤ) then 1 else 0)
: S.det = putnam_2023_b6_solution n := by
  have hentry : ∀ i j : Fin n,
      ((_root_.S n).map (Nat.cast : ℕ → ℤ)) i j =
        ∑' a : ℕ, ∑' b : ℕ,
          if a * (i.1 + 1) + b * (j.1 + 1) = (n : ℤ) then 1 else 0 := by
    intro i j
    have hi : 0 < i.val + 1 := by omega
    have hj : 0 < j.val + 1 := by omega
    change (s n (i.val + 1) (j.val + 1) : ℤ) = _
    simp only [s]
    rw [Finset.card_filter, Nat.cast_sum, Finset.product_eq_sprod,
      Finset.sum_product]
    push_cast
    symm
    rw [tsum_eq_sum (s := Finset.range (n / (i.val + 1) + 1))]
    · apply Finset.sum_congr rfl
      intro a ha
      rw [tsum_eq_sum (s := Finset.range (n / (j.val + 1) + 1))]
      · apply Finset.sum_congr rfl
        intro b hb
        norm_cast
      · intro b hb
        simp only [Finset.mem_range, not_lt] at hb
        split_ifs with h
        · have hab : a * (i.val + 1) + b * (j.val + 1) = n := by
            exact_mod_cast h
          have hdiv : n / (j.val + 1) < b := by omega
          have hlt : n < b * (j.val + 1) :=
            (Nat.div_lt_iff_lt_mul hj).mp hdiv
          omega
        · rfl
    · intro a ha
      simp only [Finset.mem_range, not_lt] at ha
      rw [show (fun b : ℕ =>
          if a * (i.1 + 1) + b * (j.1 + 1) = (n : ℤ) then 1 else 0) =
          fun _ => (0 : ℤ) by
        funext b
        split_ifs with h
        · have hab : a * (i.val + 1) + b * (j.val + 1) = n := by
            exact_mod_cast h
          have hdiv : n / (i.val + 1) < a := by omega
          have hlt : n < a * (i.val + 1) :=
            (Nat.div_lt_iff_lt_mul hi).mp hdiv
          omega
        · rfl]
      exact tsum_zero
  have hmatrix : S = ((_root_.S n).map (Nat.cast : ℕ → ℤ)) := by
    ext i j
    rw [hS i j, hentry i j]
  have hdet := problem_statement_assumed n npos
  have hpos : 0 < n / 2 + n % 2 := by omega
  have hn_div : n = n / 2 * 2 + n % 2 := by
    rw [Nat.mul_comm]
    exact (Nat.div_add_mod n 2).symm
  have hmod : n % 2 < 2 := Nat.mod_lt _ (by omega)
  have hceil : ⌈(n / 2 : ℚ)⌉₊ = n / 2 + n % 2 := by
    have hr : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hr with hr | hr
    · have hn_even : n = 2 * (n / 2) := by omega
      rw [hr, Nat.add_zero, hn_even]
      norm_num
    · have hn_odd : n = 2 * (n / 2) + 1 := by omega
      have hd : (2 * (n / 2) + 1) / 2 = n / 2 := by omega
      rw [hr, hn_odd]
      rw [hd]
      apply (Nat.ceil_eq_iff (by omega)).2
      constructor <;> norm_num [div_eq_mul_inv] <;> linarith
  rw [hmatrix, hdet]
  simp only [putnam_2023_b6_solution, hceil]
  have hexp : n / 2 + n % 2 + 1 = (n / 2 + n % 2 - 1) + 2 := by omega
  rw [hexp, pow_add]
  norm_num
