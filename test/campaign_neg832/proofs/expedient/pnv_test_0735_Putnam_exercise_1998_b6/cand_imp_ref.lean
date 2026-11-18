import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a b c : ℤ} : ∃ n : ℕ, ¬∃ m : ℕ, m^2 = n^3 + a * n^2 + b * n + c := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1998_b6 (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  let N : ℤ := a^2 + b^2 + c^2 + 1
  obtain ⟨n, hn⟩ := dummy_assumed (a := 3*N + a)
    (b := 3*N^2 + 2*a*N + b) (c := N^3 + a*N^2 + b*N + c)
  refine ⟨(n : ℤ) + N, ?_, ?_⟩
  · dsimp [N]
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  rintro ⟨m, hm⟩
  have hx : (1 : ℤ) ≤ (n : ℤ) + N := by
    dsimp [N]
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  have hxa : b^2 + c^2 ≤ (n : ℤ) + N + a := by
    dsimp [N] at hx ⊢
    nlinarith [sq_nonneg (2*a + 1)]
  have hb : 0 ≤ b^2 + b := by
    nlinarith [sq_nonneg (2*b + 1)]
  have hc : 0 ≤ c^2 + c := by
    nlinarith [sq_nonneg (2*c + 1)]
  have hp : 0 ≤ ((n : ℤ) + N)^3 + a*((n : ℤ) + N)^2 +
      b*((n : ℤ) + N) + c := by
    have hx0 : 0 ≤ (n : ℤ) + N := by omega
    have hx1 : 0 ≤ (n : ℤ) + N - 1 := by omega
    have hxx := mul_nonneg hx0 hx1
    have hxa0 : 0 ≤ (n : ℤ) + N + a - b^2 - c^2 := by omega
    have h1 := mul_nonneg (sq_nonneg ((n : ℤ) + N)) hxa0
    have h2 := mul_nonneg hb hx0
    have h3 := mul_nonneg (sq_nonneg b)
      (show 0 ≤ ((n : ℤ) + N)^2 - ((n : ℤ) + N) by nlinarith)
    have h4 := mul_nonneg (sq_nonneg c)
      (show 0 ≤ ((n : ℤ) + N)^2 - 1 by nlinarith)
    nlinarith
  have hm0 : 0 ≤ m := by
    exact_mod_cast (hm ▸ Real.sqrt_nonneg _)
  apply hn
  refine ⟨m.toNat, ?_⟩
  have hm' : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm0
  have hpR : (0 : ℝ) ≤
      (((n : ℤ) + N)^3 + a*((n : ℤ) + N)^2 + b*((n : ℤ) + N) + c : ℤ) := by
    exact_mod_cast hp
  have hsqrt := Real.sq_sqrt hpR
  push_cast at hm hsqrt
  rw [hm] at hsqrt
  have hsqrtZ : m^2 = ((n : ℤ) + N)^3 + a*((n : ℤ) + N)^2 +
      b*((n : ℤ) + N) + c := by
    exact_mod_cast hsqrt
  rw [← hm'] at hsqrtZ
  norm_num at hsqrtZ ⊢
  ring_nf at hsqrtZ ⊢
  exact hsqrtZ
