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
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hNat : limsup (fun n : ℕ => (n : ℝ)) atTop = 0 := by
    rw [Filter.limsup_eq]
    have hempty : {x : ℝ | ∀ᶠ n : ℕ in atTop, (n : ℝ) ≤ x} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hx
      have hgt : ∀ᶠ n : ℕ in atTop, x < (n : ℝ) :=
        hcast (eventually_gt_atTop x)
      obtain ⟨n, hnx, hxn⟩ := (hx.and hgt).exists
      exact (not_lt_of_ge hnx) hxn
    rw [hempty]
    simp
  have htoBot : Tendsto (fun n : ℕ => 1 - (n : ℝ)) atTop atBot := by
    refine tendsto_atBot.2 ?_
    intro x
    have hge : ∀ᶠ n : ℕ in atTop, 1 - x ≤ (n : ℝ) :=
      hcast (eventually_ge_atTop (1 - x))
    filter_upwards [hge] with n hn
    linarith
  have hSub : limsup (fun n : ℕ => 1 - (n : ℝ)) atTop = 0 := by
    rw [Filter.limsup_eq]
    have huniv : {x : ℝ | ∀ᶠ n : ℕ in atTop, 1 - (n : ℝ) ≤ x} = Set.univ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact htoBot (eventually_le_atBot x)
    rw [huniv]
    simp
  have h := dummy_assumed
    (f := fun n : ℕ => (n : ℝ))
    (g := fun n : ℕ => 1 - (n : ℝ))
  have h' := h atTop
  change limsup (fun n : ℕ => (n : ℝ) + (1 - (n : ℝ))) atTop ≤
    limsup (fun n : ℕ => (n : ℝ)) atTop +
      limsup (fun n : ℕ => 1 - (n : ℝ)) atTop at h'
  rw [hNat, hSub] at h'
  have hone : limsup (fun n : ℕ => (n : ℝ) + (1 - (n : ℝ))) atTop = 1 := by
    have heq : ∀ᶠ n : ℕ in atTop,
        (n : ℝ) + (1 - (n : ℝ)) = (fun _ : ℕ => (1 : ℝ)) n :=
      Eventually.of_forall (fun n : ℕ => by ring)
    rw [Filter.limsup_congr heq]
    exact limsup_const (f := (atTop : Filter ℕ)) (1 : ℝ)
  rw [hone] at h'
  norm_num at h'
