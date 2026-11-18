import Mathlib

open Finset

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  ∀ (a : ℕ → ℕ),
    (∀ k, a k > 0) →
    (∀ i j, i ≠ j → a i ≠ a j) →
    ∀ n : ℕ, n ≥ 1 →
      ∑ k ∈ Finset.Icc 1 n, (a k : ℚ) / (k : ℚ)^2 ≥ ∑ k ∈ Finset.Icc 1 n, (1 : ℚ) / (k : ℚ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1978_p5
    (n : ℕ)
    (f : ℕ → ℕ)
    (h₀ : ∀ (m : ℕ), 0 < m → 0 < f m)
    (h₁ : ∀ (p q : ℕ), 0 < p → 0 < q → p ≠ q → f p ≠ f q)
    (h₂ : 0 < n) :
    ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k ≤ ∑ k ∈ Finset.Icc 1 n, ((f k):ℝ) / k ^ 2 := by
  let e : ℕ → ℕ := fun k => if k = 0 then n + 1 else if k ≤ n then k else k + 1
  have he_pos : ∀ k, 0 < e k := by
    intro k
    by_cases hk : k = 0
    · simp only [e, hk, if_pos]
      omega
    · simp only [e, hk, if_false]
      split <;> omega
  have he_inj : Function.Injective e := by
    intro i j hij
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · exact hi.trans hj.symm
      · simp only [e, hi, hj, if_pos, if_false] at hij
        split at hij <;> omega
    · by_cases hj : j = 0
      · simp only [e, hi, hj, if_pos, if_false] at hij
        split at hij <;> omega
      · simp only [e, hi, hj, if_false] at hij
        split at hij <;> split at hij <;> omega
  have he_eq : ∀ (k : ℕ), k ∈ Finset.Icc 1 n → e k = k := by
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    simp only [e]
    rw [if_neg (Nat.ne_of_gt hk'.1), if_pos hk'.2]
  let a : ℕ → ℕ := fun k => f (e k)
  have ha_pos : ∀ k, a k > 0 := by
    intro k
    exact h₀ (e k) (he_pos k)
  have ha_inj : ∀ i j, i ≠ j → a i ≠ a j := by
    intro i j hij
    exact h₁ (e i) (e j) (he_pos i) (he_pos j) (he_inj.ne hij)
  have h := problem_statement_assumed a ha_pos ha_inj n h₂
  have hsum : (∑ k ∈ Finset.Icc 1 n, (a k : ℚ) / (k : ℚ)^2) =
      ∑ k ∈ Finset.Icc 1 n, (f k : ℚ) / (k : ℚ)^2 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [show a k = f k by simp only [a, he_eq k hk]]
  rw [hsum] at h
  have h' : (∑ k ∈ Finset.Icc 1 n, (1 : ℚ) / (k : ℚ)) ≤
      ∑ k ∈ Finset.Icc 1 n, (f k : ℚ) / (k : ℚ)^2 := h
  rw [← Rat.cast_le (K := ℝ)] at h'
  simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_natCast, Rat.cast_pow,
    Rat.cast_one] using h'
