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
      (s n i j : ℤ) =
        ∑' a : ℕ, ∑' b : ℕ, if a * i + b * j = (n : ℤ) then 1 else 0 := by
    unfold s
    rw [← Finset.sum_boole]
    change (∑ x ∈ (Finset.range (n / i + 1)).product (Finset.range (n / j + 1)),
      (if x.1 * i + x.2 * j = n then 1 else 0 : ℤ)) = _
    refine (Finset.sum_product (Finset.range (n / i + 1)) (Finset.range (n / j + 1))
      (fun x => (if x.1 * i + x.2 * j = n then 1 else 0 : ℤ))).trans ?_
    rw [tsum_eq_sum (s := Finset.range (n / i + 1))]
    · apply Finset.sum_congr rfl
      intro a ha
      rw [tsum_eq_sum (s := Finset.range (n / j + 1))]
      · apply Finset.sum_congr rfl
        intro b hb
        have hcast : ((a : ℤ) * i + b * j = n) ↔ (a * i + b * j = n) := by
          norm_cast
        simp [hcast]
      · intro b hb
        simp only [Finset.mem_range, not_lt] at hb
        split
        · rename_i h
          norm_cast at h
          have hle : b * j ≤ n := by omega
          have := (Nat.le_div_iff_mul_le hj).2 hle
          omega
        · rfl
    · intro a ha
      simp only [Finset.mem_range, not_lt] at ha
      calc
        _ = ∑' _ : ℕ, (0 : ℤ) := by
          apply tsum_congr
          intro b
          show (if (a : ℤ) * i + b * j = n then 1 else 0) = 0
          split
          · rename_i h
            norm_cast at h
            have hle : a * i ≤ n := by omega
            have := (Nat.le_div_iff_mul_le hi).2 hle
            omega
          · rfl
        _ = 0 := tsum_zero
  have hanswer : putnam_2023_b6_solution n =
      ((-1 : ℤ) ^ ((n / 2 + (n % 2)) - 1) * 2 * (n / 2 + (n % 2))) := by
    have hnform : n = 2 * (n / 2) + n % 2 := by omega
    have hr : n % 2 = 0 ∨ n % 2 = 1 := by omega
    have hc : ⌈(n / 2 : ℚ)⌉₊ = n / 2 + n % 2 := by
      rcases hr with hr | hr
      · rw [hnform, hr]
        norm_num [add_div]
      · rw [hnform, hr]
        norm_num [add_div]
        rw [add_comm, Nat.ceil_add_natCast (by positivity)]
        norm_num
        omega
    unfold putnam_2023_b6_solution
    rw [hc]
    have hk : 0 < n / 2 + n % 2 := by omega
    have he : n / 2 + n % 2 + 1 = (n / 2 + n % 2 - 1) + 2 := by omega
    rw [he, pow_add]
    norm_num
  calc
    Matrix.det ((S n).map (Nat.cast : ℕ → ℤ)) = putnam_2023_b6_solution n := by
      apply putnam_2023_b6_assumed n _ hn
      intro i j
      exact hcount (i.1 + 1) (j.1 + 1) (by omega) (by omega)
    _ = _ := hanswer
