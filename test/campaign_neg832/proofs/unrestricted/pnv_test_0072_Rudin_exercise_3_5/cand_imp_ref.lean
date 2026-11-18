import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (a b : ℕ → ℝ) : limsup (a + b) ≤ limsup a + limsup b := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_5
    (a b : ℕ → EReal)
    (hareal : ∀ n, a n ≠ ⊤ ∧ a n ≠ ⊥)
    (hbreal : ∀ n, b n ≠ ⊤ ∧ b n ≠ ⊥)
    (ha : limsup a ≠ ⊤)
    (hb : limsup b ≠ ⊥) :
    limsup (λ n => a n + b n) ≤ limsup a + limsup b := by
  exfalso
  have hpos : limsup (fun n : ℕ => (n : ℝ)) atTop = 0 := by
    rw [limsup_eq]
    have hempty : {x : ℝ | ∀ᶠ n : ℕ in atTop, (n : ℝ) ≤ x} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hx
      obtain ⟨N, hN⟩ := eventually_atTop.1 hx
      obtain ⟨m, hm⟩ := exists_nat_gt x
      have hle := hN (m + N) (Nat.le_add_left N m)
      exact (not_le_of_gt (lt_of_lt_of_le hm (Nat.cast_le.2 (Nat.le_add_right m N)))) hle
    rw [hempty]
    exact Real.sInf_empty
  have hneg : limsup (fun n : ℕ => (1 : ℝ) - n) atTop = 0 := by
    rw [limsup_eq]
    have huniv : {x : ℝ | ∀ᶠ n : ℕ in atTop, (1 : ℝ) - n ≤ x} = Set.univ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      obtain ⟨N, hN⟩ := exists_nat_ge (1 - x)
      filter_upwards [eventually_ge_atTop N] with n hn
      have hcast : (N : ℝ) ≤ n := Nat.cast_le.2 hn
      linarith
    rw [huniv]
    exact Real.sInf_univ
  have h := dummy_assumed (fun n : ℕ => (n : ℝ)) (fun n : ℕ => (1 : ℝ) - n) atTop
  change limsup ((fun n : ℕ => (n : ℝ)) + (fun n : ℕ => (1 : ℝ) - n)) atTop ≤
    limsup (fun n : ℕ => (n : ℝ)) atTop + limsup (fun n : ℕ => (1 : ℝ) - n) atTop at h
  rw [show (fun n : ℕ => (n : ℝ)) + (fun n : ℕ => (1 : ℝ) - n) =
      (fun _ : ℕ => (1 : ℝ)) by funext n; simp] at h
  have hone : limsup (fun _ : ℕ => (1 : ℝ)) atTop = 1 := by
    exact Filter.limsup_const 1
  rw [hone, hpos, hneg] at h
  norm_num at h
