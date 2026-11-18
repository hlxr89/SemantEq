import Mathlib

open Nat Set MeasureTheory Topology Filter

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem putnam_1973_b3_assumed
(p : ℕ)
(pgt1 : p > 1)
(hprime : ∀ x ∈ Set.Ico 0 p, Nat.Prime (x^2 - x + p))
: ∃! triple : ℤ × ℤ × ℤ, let (a,b,c) := triple; b^2 - 4*a*c = 1 - 4*p ∧ 0 < a ∧ a ≤ c ∧ -a ≤ b ∧ b < a :=
by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (p : ℤ) (hp : p > 1) 
  (h_prime : ∀ x : ℤ, 0 < x ∧ x < p → Nat.Prime (Int.natAbs (x^2 - x + p))) :
  ∃! triple : ℤ × ℤ × ℤ, 
    let (a, b, c) := triple
    b^2 - 4*a*c = 1 - 4*p ∧ 0 < a ∧ a ≤ c ∧ -a ≤ b ∧ b < a := by
  have hp0 : 0 ≤ p := by omega
  have hp_cast : ((p.natAbs : ℕ) : ℤ) = p := by simp [Int.natAbs_of_nonneg hp0]
  apply hp_cast ▸ putnam_1973_b3_assumed p.natAbs (by omega)
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    simpa [Int.natAbs_of_nonneg hp0] using h_prime 1 (by omega)
  · have hxp : (x : ℤ) < p := by
      rw [← hp_cast]
      exact_mod_cast hx.2
    have h := h_prime (x : ℤ) (by omega)
    have hxle : x ≤ x ^ 2 := by nlinarith [Nat.one_le_iff_ne_zero.mpr hx0]
    have hsub : ((x ^ 2 - x : ℕ) : ℤ) = (x : ℤ) ^ 2 - x := by
      rw [Nat.cast_sub hxle]
      norm_num
    have hnonneg : 0 ≤ (x : ℤ) ^ 2 - x + p := by
      rw [← hsub, ← hp_cast]
      positivity
    have hcast : ((x ^ 2 - x + p.natAbs : ℕ) : ℤ) =
        (x : ℤ) ^ 2 - x + p := by
      push_cast [Nat.cast_sub hxle]
      rw [abs_of_nonneg hp0]
    have heq : Int.natAbs ((x : ℤ) ^ 2 - x + p) = x ^ 2 - x + p.natAbs := by
      omega
    rw [heq] at h
    exact h
