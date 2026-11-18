import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {n : ℤ} (hn₁ : n > 3) (hn₂ : Nat.Prime (Int.natAbs n)) (hn₃ : ¬(∃ k, k ^ 2 = n)) (a : ℤ√(-n)) (ha₁ : a ≠ 0) (ha₂ : a.norm < n) : Irreducible a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_8_3_5a {n : ℤ} (hn0 : n > 3) (hn1 : Squarefree n) :
  Irreducible (2 : Zsqrtd $ -n) ∧
  Irreducible (⟨0, 1⟩ : Zsqrtd $ -n) ∧
  Irreducible (1 + ⟨0, 1⟩ : Zsqrtd $ -n) := by
  exfalso
  have hnsq : ¬(∃ k : ℤ, k ^ 2 = 37) := by
    rintro ⟨k, hk⟩
    have hlo : -7 < k := by nlinarith
    have hhi : k < 7 := by nlinarith
    interval_cases k <;> norm_num at hk
  have hbad : Irreducible (6 : ℤ√(-37)) :=
    dummy_assumed (n := 37) (by norm_num) (by norm_num) hnsq 6
      (by norm_num [Zsqrtd.ext_iff]) (by norm_num [Zsqrtd.norm])
  have h2 : ¬IsUnit (2 : ℤ√(-37)) := by
    rw [← Zsqrtd.norm_eq_one_iff]
    norm_num [Zsqrtd.norm]
  have h3 : ¬IsUnit (3 : ℤ√(-37)) := by
    rw [← Zsqrtd.norm_eq_one_iff]
    norm_num [Zsqrtd.norm]
  exact (hbad.isUnit_or_isUnit (by norm_num : (6 : ℤ√(-37)) = 2 * 3)).elim h2 h3
