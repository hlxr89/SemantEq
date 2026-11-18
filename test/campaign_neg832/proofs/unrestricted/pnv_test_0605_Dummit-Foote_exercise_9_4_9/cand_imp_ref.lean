import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R] (x : R) (hx : x ≠ 0) (hx' : ∀ y : R, y * y = 2 → y = x ∨ y = -x) : Irreducible (X^2 - C x) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_4_9 :
  Irreducible (X^2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) := by
  letI : Zsqrtd.Nonsquare 2 := ⟨by
    intro n hn
    apply Nat.not_exists_sq' (m := 1) (n := 2) (by norm_num) (by norm_num)
    exact ⟨n, by simpa [pow_two] using hn.symm⟩⟩
  letI : NoZeroDivisors (Zsqrtd 2) :=
    ⟨fun h => Zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero h⟩
  letI : IsDomain (Zsqrtd 2) := NoZeroDivisors.to_isDomain _
  have hmonic : (X^2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)).Monic := by
    exact monic_X_pow_sub_C _ (by norm_num)
  rw [hmonic.irreducible_iff_roots_eq_zero_of_degree_le_three]
  · rw [Multiset.eq_zero_iff_forall_notMem]
    intro y hy
    have hroot := (mem_roots hmonic.ne_zero).mp hy
    have him := congrArg Zsqrtd.im hroot
    simp [eval_sub, pow_two, Zsqrtd.im_mul] at him
    rw [mul_comm y.im y.re] at him
    omega
  · norm_num
  · norm_num
