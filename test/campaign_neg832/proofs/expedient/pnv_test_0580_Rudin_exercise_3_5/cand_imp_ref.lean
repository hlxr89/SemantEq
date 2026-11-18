import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f g : ℕ → ℝ} : limsup (fun n => f n + g n) ≤ limsup f + limsup g := by
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
  have hf : ¬ IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => (n : ℝ)) := by
    rintro ⟨C, hC⟩
    rw [eventually_map] at hC
    obtain ⟨N, hN⟩ := eventually_atTop.1 hC
    obtain ⟨n, hn⟩ := exists_nat_gt C
    exact (not_le_of_gt hn) ((Nat.cast_le.mpr (le_max_right N n)).trans
      (hN (max N n) (le_max_left _ _)))
  have hg : ¬ IsCoboundedUnder (· ≤ ·) atTop (fun n : ℕ => 1 - (n : ℝ)) := by
    rintro ⟨C, hC⟩
    obtain ⟨n, hn⟩ := exists_nat_gt (2 - C)
    have hev : ∀ᶠ m : ℕ in atTop, 1 - (m : ℝ) ≤ C - 1 := by
      filter_upwards [eventually_ge_atTop n] with m hm
      have hnm : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have h := hC (C - 1) (by simpa only [eventually_map] using hev)
    linarith
  have h := dummy_assumed (f := fun n : ℕ => (n : ℝ))
    (g := fun n => 1 - (n : ℝ)) atTop
  change limsup (fun n : ℕ => (n : ℝ) + (1 - (n : ℝ))) atTop ≤
    limsup (fun n : ℕ => (n : ℝ)) atTop + limsup (fun n : ℕ => 1 - (n : ℝ)) atTop at h
  rw [Real.limsup_of_not_isBoundedUnder hf, Real.limsup_of_not_isCoboundedUnder hg] at h
  norm_num at h
