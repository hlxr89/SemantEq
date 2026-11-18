import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
def S : ℚ := Finset.sum (Finset.range 1319) (fun k => ((-1 : ℚ) ^ k) / (k + 1 : ℚ))

-- ===== assumed statement (antecedent) =====
theorem imo1979_p1_assumed (p q : ℤ) (hp : 0 < p) (hq : 0 < q)
    (h : (p : ℚ) / q = ∑ i ∈ Finset.range 1319, (-1 : ℚ)^i / (i + 1)) :
    1979 ∣ p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement :
  ∃ p q : ℕ, p > 0 ∧ q > 0 ∧ S = (p : ℚ) / (q : ℚ) ∧ Nat.gcd p q = 1 ∧ 1979 ∣ p := by
  have hpair (n : ℕ) :
      0 < ((-1 : ℚ) ^ (2 * n)) / ((2 * n : ℕ) + 1 : ℚ) +
        ((-1 : ℚ) ^ (2 * n + 1)) / ((2 * n + 1 : ℕ) + 1 : ℚ) := by
    rw [show (-1 : ℚ) ^ (2 * n) = 1 by
      rw [pow_mul]
      norm_num]
    rw [show (-1 : ℚ) ^ (2 * n + 1) = -1 by
      rw [pow_add, pow_mul, pow_one]
      norm_num]
    norm_num only [one_div, neg_div]
    rw [← sub_eq_add_neg, sub_pos]
    have ht : 1 / (2 * (n : ℚ) + 2) < 1 / (2 * (n : ℚ) + 1) :=
      one_div_lt_one_div_of_lt (by positivity) (by norm_num)
    convert ht using 1 <;> norm_num only [one_div, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat] <;> ring
  have heven : ∀ n : ℕ, 0 ≤ Finset.sum (Finset.range (2 * n))
      (fun k => ((-1 : ℚ) ^ k) / (k + 1 : ℚ)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 2 by omega]
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      linarith [hpair n]
  have hS : 0 < S := by
    have he := heven 659
    norm_num only at he
    rw [S, show 1319 = 1318 + 1 by norm_num, Finset.sum_range_succ]
    norm_num [show (-1 : ℚ) ^ 1318 = 1 by norm_num]
  have hnum : 0 < S.num := Rat.num_pos.mpr hS
  have hden : 0 < S.den := Rat.den_pos S
  have href : (1979 : ℤ) ∣ S.num := by
    apply imo1979_p1_assumed S.num S.den hnum
    · exact_mod_cast hden
    · change (S.num : ℚ) / (S.den : ℚ) = S
      exact Rat.num_div_den S
  refine ⟨S.num.natAbs, S.den, ?_, hden, ?_, Rat.reduced S, ?_⟩
  · exact Int.natAbs_pos.mpr (ne_of_gt hnum)
  · have hcast : (S.num.natAbs : ℤ) = S.num := by
      rw [Int.natCast_natAbs, abs_of_pos hnum]
    have hcastQ : (S.num.natAbs : ℚ) = (S.num : ℚ) := by
      calc
        (S.num.natAbs : ℚ) = ((S.num.natAbs : ℤ) : ℚ) := by
          rw [Int.cast_natCast]
        _ = (S.num : ℚ) := congrArg (fun z : ℤ => (z : ℚ)) hcast
    rw [hcastQ, Rat.num_div_den]
  · have hcast : (S.num.natAbs : ℤ) = S.num := by
      rw [Int.natCast_natAbs, abs_of_pos hnum]
    rw [← hcast] at href
    exact_mod_cast href
