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

lemma s_cast_eq_tsum (n i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
    (s n i j : ℤ) =
      ∑' a : ℕ, ∑' b : ℕ, if a * i + b * j = (n : ℤ) then 1 else 0 := by
  classical
  have hinner (a : ℕ) :
      (∑' b : ℕ, if a * i + b * j = (n : ℤ) then (1 : ℤ) else 0) =
        ∑ b ∈ Finset.range (n / j + 1),
          if a * i + b * j = (n : ℤ) then (1 : ℤ) else 0 := by
    apply tsum_eq_sum
    intro b hb
    simp only [Finset.mem_range, not_lt] at hb
    split_ifs with h
    · have hnat : a * i + b * j = n := by exact_mod_cast h
      have hle : b * j ≤ n := by omega
      have hdiv : b ≤ n / j := (Nat.le_div_iff_mul_le hj).2 hle
      omega
    · rfl
  have houter :
      (∑' a : ℕ, ∑' b : ℕ, if a * i + b * j = (n : ℤ) then (1 : ℤ) else 0) =
        ∑ a ∈ Finset.range (n / i + 1),
          ∑' b : ℕ, if a * i + b * j = (n : ℤ) then (1 : ℤ) else 0 := by
    apply tsum_eq_sum
    intro a ha
    simp only [Finset.mem_range, not_lt] at ha
    rw [hinner]
    apply Finset.sum_eq_zero
    intro b hb
    split_ifs with h
    · have hnat : a * i + b * j = n := by exact_mod_cast h
      have hle : a * i ≤ n := by omega
      have hdiv : a ≤ n / i := (Nat.le_div_iff_mul_le hi).2 hle
      omega
    · rfl
  conv_rhs => rw [houter]
  simp_rw [hinner]
  simp only [s, Finset.sum_boole]
  norm_cast
  rw [Finset.card_filter]
  simp_rw [Finset.card_filter]
  exact Finset.sum_product (Finset.range (n / i + 1)) (Finset.range (n / j + 1))
    (fun p : ℕ × ℕ => if p.1 * i + p.2 * j = n then (1 : ℕ) else 0)

lemma solution_forms_eq (n : ℕ) (hn : 0 < n) :
    putnam_2023_b6_solution n =
      ((-1 : ℤ) ^ ((n / 2 + (n % 2)) - 1) * 2 * (n / 2 + (n % 2))) := by
  have hc : ⌈(n / 2 : ℚ)⌉₊ = n / 2 + n % 2 := by
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · norm_num
    · norm_num [Nat.cast_add, Nat.cast_mul]
      rw [show ((2 * (k : ℚ) + 1) / 2) = k + 1 / 2 by ring]
      rw [add_comm, Nat.ceil_add_natCast (by norm_num)]
      norm_num
      omega
  change (-1 : ℤ) ^ (⌈(n / 2 : ℚ)⌉₊ + 1) * 2 * ⌈(n / 2 : ℚ)⌉₊ =
    ((-1 : ℤ) ^ ((n / 2 + (n % 2)) - 1) * 2 * (n / 2 + (n % 2)))
  rw [hc]
  have hp : 0 < n / 2 + n % 2 := by omega
  have he : (n / 2 + n % 2 + 1) % 2 = (n / 2 + n % 2 - 1) % 2 := by omega
  have hpow : (-1 : ℤ) ^ (n / 2 + n % 2 + 1) =
      (-1 : ℤ) ^ (n / 2 + n % 2 - 1) := by
    calc
      _ = (-1 : ℤ) ^ ((n / 2 + n % 2 + 1) % 2) := neg_one_pow_eq_pow_mod_two _
      _ = (-1 : ℤ) ^ ((n / 2 + n % 2 - 1) % 2) := by rw [he]
      _ = _ := (neg_one_pow_eq_pow_mod_two _).symm
  rw [hpow]
  norm_num [Nat.cast_add]

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (n : ℕ) (hn : 0 < n) :
  Matrix.det ((S n).map (Nat.cast : ℕ → ℤ)) = 
    ((-1 : ℤ) ^ ((n / 2 + (n % 2)) - 1) * 2 * (n / 2 + (n % 2))) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_2023_b6
(n : ℕ)
(S : Matrix (Fin n) (Fin n) ℤ)
(npos : n > 0)
(hS : ∀ i j : Fin n, S i j = ∑' a : ℕ, ∑' b : ℕ, if a * (i.1 + 1) + b * (j.1 + 1) = (n : ℤ) then 1 else 0)
: S.det = putnam_2023_b6_solution n := by
  have hmatrix : S = ((_root_.S n).map (Nat.cast : ℕ → ℤ)) := by
    funext i j
    exact (hS i j).trans
      (s_cast_eq_tsum n (i.1 + 1) (j.1 + 1) (by omega) (by omega)).symm
  rw [hmatrix, problem_statement_assumed n npos]
  exact (solution_forms_eq n npos).symm

