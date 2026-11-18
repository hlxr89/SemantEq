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
  Matrix.det ((S n).map (Nat.cast : ℕ → ℤ)) = 
    ((-1 : ℤ) ^ ((n / 2 + (n % 2)) - 1) * 2 * (n / 2 + (n % 2))) := by
  have hcount (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
      (∑' a : ℕ, ∑' b : ℕ, if a * i + b * j = n then (1 : ℤ) else 0) = (s n i j : ℤ) := by
    unfold s
    rw [tsum_eq_sum (s := Finset.range (n / i + 1))]
    · apply Eq.trans ?_ (Finset.sum_boole _ _)
      apply Eq.trans ?_ (Finset.sum_product _ _ _).symm
      apply Finset.sum_congr rfl
      intro a ha
      rw [tsum_eq_sum (s := Finset.range (n / j + 1))]
      intro b hb
      simp only [Finset.mem_range, not_lt] at hb
      rw [if_neg]
      intro hab
      have hbj : n < b * j := by
        rw [← Nat.div_lt_iff_lt_mul hj]
        exact lt_of_lt_of_le (Nat.lt_add_one _) hb
      exact (not_lt_of_ge (hab ▸ Nat.le_add_left (b * j) (a * i))) hbj
    · intro a ha
      simp only [Finset.mem_range, not_lt] at ha
      have hz : (fun b : ℕ => if a * i + b * j = n then (1 : ℤ) else 0) = fun _ => 0 := by
        funext b
        rw [if_neg]
        intro hab
        have hai : n < a * i := by
          rw [← Nat.div_lt_iff_lt_mul hi]
          exact lt_of_lt_of_le (Nat.lt_add_one _) ha
        exact (not_lt_of_ge (hab ▸ Nat.le_add_right (a * i) (b * j))) hai
      rw [hz, tsum_zero]
  have hmatrix : ((S n).map (Nat.cast : ℕ → ℤ)) = fun i j =>
      ∑' a : ℕ, ∑' b : ℕ, if a * (i.1 + 1) + b * (j.1 + 1) = (n : ℤ) then 1 else 0 := by
    funext i j
    rw [show ((S n).map (Nat.cast : ℕ → ℤ)) i j = (s n (i.1 + 1) (j.1 + 1) : ℤ) by rfl]
    rw [← hcount (i.1 + 1) (j.1 + 1) (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)]
    congr 2
    funext a
    apply tsum_congr
    intro b
    congr 1
    norm_cast
  have hdet := putnam_2023_b6_assumed n ((S n).map (Nat.cast : ℕ → ℤ)) hn
    (fun i j => congrFun (congrFun hmatrix i) j)
  have hceil : ⌈(n / 2 : ℚ)⌉₊ = n / 2 + n % 2 := by
    rw [← Int.ceil_toNat]
    change ⌈(n : ℚ) / (2 : ℕ)⌉.toNat = n / 2 + n % 2
    rw [Rat.ceil_natCast_div_natCast]
    omega -- non-rewrite step
  have hkpos : 0 < n / 2 + n % 2 := by omega -- non-rewrite step
  unfold putnam_2023_b6_solution at hdet
  rw [hceil] at hdet
  have hexponent : n / 2 + n % 2 + 1 = (n / 2 + n % 2 - 1) + 2 := by
    conv_lhs => rw [← Nat.sub_add_cancel hkpos]
  rw [hexponent, pow_add, show ((-1 : ℤ) ^ 2) = 1 by rfl, mul_one] at hdet
  exact hdet
