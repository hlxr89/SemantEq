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
  have hp_nonneg : 0 ≤ p := by omega
  have hp_cast : (p.natAbs : ℤ) = p := Int.natAbs_of_nonneg hp_nonneg
  have hp_nat : p.natAbs > 1 := by omega
  have hprime_nat : ∀ x ∈ Set.Ico 0 p.natAbs, Nat.Prime (x^2 - x + p.natAbs) := by
    intro x hx
    by_cases hx0 : x = 0
    · subst x
      have h := h_prime 1 (by omega)
      simpa [hp_cast] using h
    · have hx_pos : (0 : ℤ) < x := by exact_mod_cast (Nat.pos_of_ne_zero hx0)
      have hx_lt : (x : ℤ) < p := by
        rw [← hp_cast]
        exact_mod_cast hx.2
      have h := h_prime (x : ℤ) ⟨hx_pos, hx_lt⟩
      have hx_sq : x ≤ x^2 := by nlinarith
      have hpoly : ((x^2 - x + p.natAbs : ℕ) : ℤ) =
          (x : ℤ)^2 - x + p := by
        rw [Nat.cast_add, Nat.cast_sub hx_sq, hp_cast]
        norm_num
      have hpoly_natAbs : Int.natAbs ((x : ℤ)^2 - x + p) =
          x^2 - x + p.natAbs := by
        rw [← hpoly, Int.natAbs_natCast]
      rw [hpoly_natAbs] at h
      exact h
  simpa [hp_cast] using putnam_1973_b3_assumed p.natAbs hp_nat hprime_nat
