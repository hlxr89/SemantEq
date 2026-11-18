import Mathlib

open Finset

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (a : ℕ → ℕ) 
  (h_pos : ∀ k, 0 < a k)
  (h_distinct : ∀ i j, i ≠ j → a i ≠ a j) :
  ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, (a k : ℚ) / (k : ℚ)^2 ≥ ∑ k ∈ Finset.Icc 1 n, (1 : ℚ) / (k : ℚ) := by
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
    dsimp [e]
    split_ifs <;> omega
  have he_inj : Function.Injective e := by
    intro i j hij
    dsimp [e] at hij
    split_ifs at hij <;> omega
  let a : ℕ → ℕ := fun k => f (e k)
  have ha_pos : ∀ k, 0 < a k := by
    intro k
    exact h₀ (e k) (he_pos k)
  have ha_distinct : ∀ i j, i ≠ j → a i ≠ a j := by
    intro i j hij
    exact h₁ (e i) (e j) (he_pos i) (he_pos j) (he_inj.ne hij)
  have hc := problem_statement_assumed a ha_pos ha_distinct n
  have hae : ∀ k ∈ Finset.Icc 1 n, a k = f k := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkn : k ≤ n := (Finset.mem_Icc.mp hk).2
    have hk0 : k ≠ 0 := by omega
    simp [a, e, hk0, hkn]
  have hsum : ∑ k ∈ Finset.Icc 1 n, (a k : ℚ) / (k : ℚ)^2 =
      ∑ k ∈ Finset.Icc 1 n, (f k : ℚ) / (k : ℚ)^2 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hae k hk]
  have hc' : ∑ k ∈ Finset.Icc 1 n, (f k : ℚ) / (k : ℚ)^2 ≥
      ∑ k ∈ Finset.Icc 1 n, (1 : ℚ) / (k : ℚ) := by
    rw [← hsum]
    exact hc
  have hr := (Rat.cast_le (K := ℝ)).mpr hc'
  push_cast at hr
  simpa using hr
