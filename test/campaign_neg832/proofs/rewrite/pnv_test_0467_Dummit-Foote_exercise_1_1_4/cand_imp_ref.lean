import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {n : ℕ} (hn : n ≠ 0) : ∀ (a b c : ℤ), (a % n) * ((b % n) * (c % n)) = ((a % n) * (b % n)) * (c % n) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_1_4 (n : ℕ) (a b c : ZMod n) :
  (a * b) * c = a * (b * c) := by
  have nat_assoc (x y z : ℕ) : (x * y) * z = x * (y * z) := by
    let m := Nat.succ (max x (max y z))
    have hx : x < m := Nat.lt_succ_of_le (le_max_left x (max y z))
    have hy : y < m := Nat.lt_succ_of_le (le_trans (le_max_left y z) (le_max_right x (max y z)))
    have hz : z < m := Nat.lt_succ_of_le (le_trans (le_max_right y z) (le_max_right x (max y z)))
    have h := dummy_assumed (n := m) (Nat.succ_ne_zero _) (x : ℤ) (y : ℤ) (z : ℤ)
    have hxm : (x : ℤ) % (m : ℤ) = x := Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hx)
    have hym : (y : ℤ) % (m : ℤ) = y := Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hy)
    have hzm : (z : ℤ) % (m : ℤ) = z := Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hz)
    rw [hxm, hym, hzm] at h
    exact_mod_cast h.symm -- non-rewrite step
  have int_assoc (x y z : ℤ) : (x * y) * z = x * (y * z) := by
    have natCast_assoc (x y z : ℕ) : ((x : ℤ) * y) * z = x * (y * z) := by
      exact_mod_cast nat_assoc x y z -- non-rewrite step
    cases x <;> cases y <;> cases z <;>
      simp only [Int.negSucc_eq, Int.ofNat_eq_natCast, ← Int.natCast_succ,
        Int.neg_mul, Int.mul_neg, Int.neg_neg, natCast_assoc]
  cases n with
  | zero => exact int_assoc a b c
  | succ n =>
    have h := congrArg (fun x : ℕ => (x : ZMod n.succ)) (nat_assoc a.val b.val c.val)
    simpa only [Nat.cast_mul, ZMod.natCast_zmod_val] using h
