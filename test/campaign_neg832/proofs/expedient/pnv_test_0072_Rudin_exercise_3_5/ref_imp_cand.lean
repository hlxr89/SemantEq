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
theorem dummy (a b : ℕ → ℝ) : limsup (a + b) ≤ limsup a + limsup b := by
  exfalso
  have htop : limsup (fun n : ℕ => ((n : ℝ) : EReal)) atTop = ⊤ :=
    (EReal.tendsto_coe_nhds_top_iff.2 tendsto_natCast_atTop_atTop).limsup_eq
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hneg : Tendsto (fun n : ℕ => -(n : ℝ)) atTop atBot :=
    tendsto_neg_atBot_iff.2 hnat
  have hneg' : Tendsto (fun n : ℕ => ((-(n : ℝ) : ℝ) : EReal)) atTop (𝓝 ⊥) :=
    EReal.tendsto_coe_nhds_bot_iff.2 hneg
  have hbot : limsup (fun n : ℕ => ((-(n : ℝ) : ℝ) : EReal)) atTop = ⊥ :=
    hneg'.limsup_eq
  have hbot' : limsup (fun n : ℕ => -((n : ℝ) : EReal)) atTop = ⊥ := by
    simpa using hbot
  have h := exercise_3_5_assumed
    (fun n : ℕ => ((-(n : ℝ) : ℝ) : EReal))
    (fun n : ℕ => ((n : ℝ) : EReal))
    (by intro n; exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩)
    (by intro n; exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩)
    (by
      intro h
      have h' := congrFun h atTop
      change limsup (fun n : ℕ => ((-(n : ℝ) : ℝ) : EReal)) atTop = (⊤ : EReal) at h'
      rw [hbot] at h'
      exact bot_ne_top h')
    (by
      intro h
      have h' := congrFun h atTop
      change limsup (fun n : ℕ => ((n : ℝ) : EReal)) atTop = (⊥ : EReal) at h'
      rw [htop] at h'
      exact top_ne_bot h')
  have h' := h atTop
  change limsup (fun n : ℕ => -((n : ℝ) : EReal) + ((n : ℝ) : EReal)) atTop ≤
    limsup (fun n : ℕ => -((n : ℝ) : EReal)) atTop +
      limsup (fun n : ℕ => ((n : ℝ) : EReal)) atTop at h'
  rw [hbot', htop] at h'
  have hzero : (fun n : ℕ => -((n : ℝ) : EReal) + ((n : ℝ) : EReal)) =
      fun _ : ℕ => (0 : EReal) := by
    funext n
    rw [← EReal.coe_neg, ← EReal.coe_add]
    norm_num
  rw [hzero] at h'
  simpa using h'
