import Mathlib

open Nat Topology Filter

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_2023_b6_solution : ℕ → ℤ := (fun n : ℕ => (-1) ^ (⌈(n / 2 : ℚ)⌉₊ + 1) * 2 * ⌈(n / 2 : ℚ)⌉₊)

private theorem count_eq (n i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
    (∑' a : ℕ, ∑' b : ℕ, if (a * i + b * j : ℕ) = n then (1 : ℤ) else 0) =
      ((Finset.filter (fun p : ℕ × ℕ => p.1 * i + p.2 * j = n)
        (Finset.product (Finset.range (n + 1)) (Finset.range (n + 1)))).card : ℤ) := by
  have hs : Summable (fun p : ℕ × ℕ => if p.1 * i + p.2 * j = n then (1 : ℤ) else 0) := by
    apply summable_of_ne_finset_zero (s := Finset.product (Finset.range (n + 1)) (Finset.range (n + 1)))
    rintro ⟨a, b⟩ hab
    have hab' : ¬ (a < n + 1 ∧ b < n + 1) := by simpa using hab
    split
    · rename_i h
      by_cases ha : a < n + 1
      · have hb : n + 1 ≤ b := by omega
        nlinarith
      · have ha' : n + 1 ≤ a := by omega
        nlinarith
    · rfl
  rw [← hs.tsum_prod]
  rw [tsum_eq_sum (s := Finset.product (Finset.range (n + 1)) (Finset.range (n + 1)))]
  · exact Finset.sum_boole _ _
  · rintro ⟨a, b⟩ hab
    have hab' : ¬ (a < n + 1 ∧ b < n + 1) := by simpa using hab
    split
    · rename_i h
      by_cases ha : a < n + 1
      · have hb : n + 1 ≤ b := by omega
        nlinarith
      · have ha' : n + 1 ≤ a := by omega
        nlinarith
    · rfl

private theorem answer_eq (n : ℕ) (hn : 0 < n) :
    putnam_2023_b6_solution n =
      (-1 : ℤ) ^ ((n + 1) / 2 - 1) * 2 * ((n + 1) / 2 : ℕ) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · simp only [putnam_2023_b6_solution]
    norm_num at hn ⊢
    have hd : (2 * k + 1) / 2 = k := by omega
    rw [hd, show k + 1 = (k - 1) + 2 by omega, pow_add]
    norm_num
    norm_cast
    omega
  · simp only [putnam_2023_b6_solution]
    have hc : ⌈((2 * k + 1 : ℕ) / 2 : ℚ)⌉₊ = k + 1 := by
      rw [Nat.ceil_eq_iff (by omega)]
      constructor <;> norm_num <;> linarith
    have hd : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    rw [hc, hd, show k + 1 + 1 = (k + 1 - 1) + 2 by omega, pow_add]
    norm_num

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
  dsimp
  rw [putnam_2023_b6_assumed n _ hn]
  · exact answer_eq n hn
  · intro i j
    symm
    convert count_eq n (i.val + 1) (j.val + 1) (by omega) (by omega) using 1 <;> norm_cast
