import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_3_5_assumed
    (a b : ℕ → EReal)
    (hareal : ∀ n, a n ≠ ⊤ ∧ a n ≠ ⊥)
    (hbreal : ∀ n, b n ≠ ⊤ ∧ b n ≠ ⊥)
    (ha : limsup a ≠ ⊤)
    (hb : limsup b ≠ ⊥) :
    limsup (λ n => a n + b n) ≤ limsup a + limsup b := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {f g : ℕ → ℝ} : limsup (fun n => f n + g n) ≤ limsup f + limsup g := by
  have htop : Tendsto (fun n : ℕ => ((n : ℝ) : EReal)) atTop (𝓝 ⊤) := by
    exact EReal.tendsto_coe_atTop.comp tendsto_natCast_atTop_atTop
  have hbot : Tendsto (fun n : ℕ => -((n : ℝ) : EReal)) atTop (𝓝 ⊥) := by
    simpa using htop.neg
  have hsup : limsup (fun n : ℕ => ((n : ℝ) : EReal)) atTop = ⊤ := htop.limsup_eq
  have hinf : limsup (fun n : ℕ => -((n : ℝ) : EReal)) atTop = ⊥ := hbot.limsup_eq
  have ha : limsup (fun n : ℕ => -((n : ℝ) : EReal)) ≠ ⊤ := by
    intro h
    have h' := congrFun h atTop
    rw [hinf] at h'
    simp at h'
  have hb : limsup (fun n : ℕ => ((n : ℝ) : EReal)) ≠ ⊥ := by
    intro h
    have h' := congrFun h atTop
    rw [hsup] at h'
    simp at h'
  have h := exercise_3_5_assumed
    (fun n : ℕ => -((n : ℝ) : EReal))
    (fun n : ℕ => ((n : ℝ) : EReal))
    (by
      intro n
      constructor
      · simpa using EReal.coe_ne_bot (n : ℝ)
      · simpa using EReal.coe_ne_top (n : ℝ))
    (by
      intro n
      exact ⟨EReal.coe_ne_top (n : ℝ), EReal.coe_ne_bot (n : ℝ)⟩)
    ha hb
  have h' := h atTop
  change limsup (fun n : ℕ => -((n : ℝ) : EReal) + ((n : ℝ) : EReal)) atTop ≤
    limsup (fun n : ℕ => -((n : ℝ) : EReal)) atTop +
      limsup (fun n : ℕ => ((n : ℝ) : EReal)) atTop at h'
  have hzero : limsup (fun n : ℕ => -((n : ℝ) : EReal) + ((n : ℝ) : EReal)) atTop = 0 := by
    have heq : ∀ᶠ n : ℕ in atTop,
        -((n : ℝ) : EReal) + ((n : ℝ) : EReal) = (fun _ : ℕ => (0 : EReal)) n :=
      Eventually.of_forall (fun n : ℕ => by
        rw [← EReal.coe_neg, ← EReal.coe_add]
        norm_num)
    rw [Filter.limsup_congr heq]
    exact limsup_const (f := (atTop : Filter ℕ)) (0 : EReal)
  rw [hinf, hsup] at h'
  rw [hzero] at h'
  simp at h'
