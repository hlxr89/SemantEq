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
  have hp_nonneg : 0 ≤ p := le_of_lt (lt_trans Int.zero_lt_one hp)
  have hp_cast : (p.toNat : ℤ) = p := Int.toNat_of_nonneg hp_nonneg
  have hp_nat : p.toNat > 1 := by
    change 1 < p.toNat
    rw [← Nat.cast_lt (α := ℤ), hp_cast]
    exact hp
  have hprime_nat : ∀ x ∈ Set.Ico 0 p.toNat, Nat.Prime (x^2 - x + p.toNat) := by
    intro x hx
    by_cases hx0 : x = 0
    · subst x
      have hp_prime := h_prime 1 (by
        constructor
        · exact Int.zero_lt_one
        · exact hp)
      have hp_abs : p.natAbs = p.toNat := by
        rw [← Nat.cast_inj (R := ℤ), Int.natAbs_of_nonneg hp_nonneg, hp_cast]
      have hzero : (0 : ℕ)^2 - 0 + p.toNat = p.toNat := by
        rw [zero_pow (Nat.succ_ne_zero 1), Nat.zero_sub, Nat.zero_add]
      rw [hzero]
      simpa only [one_pow, sub_self, zero_add, hp_abs] using hp_prime
    · have hx_pos : 0 < x := Nat.pos_of_ne_zero hx0
      have hx_cast_pos : (0 : ℤ) < (x : ℤ) := by exact_mod_cast hx_pos
      have hx_cast_lt : (x : ℤ) < p := by
        rw [← hp_cast]
        exact_mod_cast hx.2
      have hx_prime := h_prime (x : ℤ) ⟨hx_cast_pos, hx_cast_lt⟩
      have hpoly : ((x^2 - x + p.toNat : ℕ) : ℤ) =
          (x : ℤ)^2 - (x : ℤ) + p := by
        rw [Nat.cast_add, Nat.cast_sub (Nat.le_pow Nat.zero_lt_two),
          Nat.cast_pow, hp_cast]
      rw [← hpoly, Int.natAbs_natCast] at hx_prime
      exact hx_prime
  simpa only [hp_cast] using putnam_1973_b3_assumed p.toNat hp_nat hprime_nat
