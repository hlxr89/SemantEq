import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_5_6_14_assumed {p m n: ℕ} (hp : p ≠ 0) (hn : n > 0)
  {F : Type*} [Field F] [CharP F p] (hm : m = p ^ n) :
  (X ^ m - X : Polynomial F).Separable := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {F : Type*} [Field F] (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p] (n : ℕ) : (∃ (x : F), x ^ (p ^ n) = x) → (∀ x y : F, x ≠ y → x ^ (p ^ n) ≠ y ^ (p ^ n)) := by
  intro _ x y hxy hpow
  have hsep := exercise_5_6_14_assumed (F := F) hp.out.ne_zero (Nat.succ_pos n)
    (m := p ^ (n + 1)) rfl
  have hneg : (-1 : F) ≠ 0 := by
    intro h
    have hone : (1 : F) = 0 := neg_eq_zero.mp h
    haveI : Subsingleton F := ⟨fun a b ↦ sub_eq_zero.mp (by
      rw [← mul_one (a - b), hone, mul_zero])⟩
    exact hsep.ne_zero (Subsingleton.elim _ _)
  have hdiffpow : (x - y) ^ (p ^ n) = 0 := by
    rw [sub_pow_char_pow, hpow, sub_self]
  have hdiff : x - y = 0 := eq_zero_of_pow_eq_zero hdiffpow
  apply hxy
  apply (mul_left_cancel₀ hneg)
  simpa [sub_eq_zero.mp hdiff]
