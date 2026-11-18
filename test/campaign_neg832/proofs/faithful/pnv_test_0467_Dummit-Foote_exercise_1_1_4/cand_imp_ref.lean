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
  by_cases hn : n = 0
  · subst n
    have hnat : ∀ x y z : ℕ, x * (y * z) = (x * y) * z := by
      intro x y z
      let m := max x (max y z) + 1
      have hm : m ≠ 0 := by omega
      have hx : x < m := by omega
      have hy : y < m := by omega
      have hz : z < m := by omega
      have h := dummy_assumed hm (x : ℤ) (y : ℤ) (z : ℤ)
      norm_num [Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ x) (by omega : (x : ℤ) < m),
        Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ y) (by omega : (y : ℤ) < m),
        Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ z) (by omega : (z : ℤ) < m)] at h
      exact_mod_cast h
    have hint : ∀ x y z : ℕ,
        ((x : ℤ) * (y : ℤ)) * (z : ℤ) = (x : ℤ) * ((y : ℤ) * (z : ℤ)) := by
      intro x y z
      exact_mod_cast (hnat x y z).symm
    cases a <;> cases b <;> cases c <;>
      (try simp only [Int.negSucc_eq, neg_mul, mul_neg, neg_neg]) <;>
      first | exact hint _ _ _ | exact congrArg Neg.neg (hint _ _ _)
  · letI : NeZero n := ⟨hn⟩
    have h := dummy_assumed hn (a.val : ℤ) (b.val : ℤ) (c.val : ℤ)
    rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast a.val_lt),
      Int.emod_eq_of_lt (by omega) (by exact_mod_cast b.val_lt),
      Int.emod_eq_of_lt (by omega) (by exact_mod_cast c.val_lt)] at h
    have h' := congrArg (fun z : ℤ => (z : ZMod n)) h
    simpa only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val] using h'.symm
