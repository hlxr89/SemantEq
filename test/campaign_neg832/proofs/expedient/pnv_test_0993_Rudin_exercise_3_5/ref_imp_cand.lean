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
theorem dummy {a b : ℕ → ℝ} (ha : BddAbove (Set.range a)) (hb : BddAbove (Set.range b)): limsup (fun n => a n + b n) ≤ limsup a + limsup b := by
  have hn : Tendsto (fun n : ℕ => -(n : ℝ)) atTop atBot :=
    tendsto_neg_atBot_iff.mpr tendsto_natCast_atTop_atTop
  have hna : Tendsto (fun n : ℕ => (-(n : ℝ) : EReal)) atTop (𝓝 ⊥) :=
    EReal.tendsto_coe_atBot.comp hn
  have hnb : Tendsto (fun n : ℕ => ((n : ℝ) : EReal)) atTop (𝓝 ⊤) :=
    EReal.tendsto_coe_atTop.comp tendsto_natCast_atTop_atTop
  have h := exercise_3_5_assumed
    (fun n : ℕ => (-(n : ℝ) : EReal))
    (fun n : ℕ => ((n : ℝ) : EReal))
    (fun n => ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩)
    (fun n => ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩)
    (by
      intro heq
      have heq' := congrFun heq atTop
      rw [hna.limsup_eq] at heq'
      exact bot_ne_top heq')
    (by
      intro heq
      have heq' := congrFun heq atTop
      rw [hnb.limsup_eq] at heq'
      exact top_ne_bot heq')
  have : False := by
    have h' := h atTop
    change Filter.limsup
        (fun n : ℕ => (-(n : ℝ) : EReal) + ((n : ℝ) : EReal)) atTop ≤
      Filter.limsup (fun n : ℕ => (-(n : ℝ) : EReal)) atTop +
        Filter.limsup (fun n : ℕ => ((n : ℝ) : EReal)) atTop at h'
    rw [hna.limsup_eq, hnb.limsup_eq] at h'
    have hz : (0 : EReal) ≤ ⊥ := by
      simpa only [← EReal.coe_neg, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero,
        limsup_const, EReal.bot_add] using h'
    exact (not_le_of_gt (EReal.bot_lt_coe 0)) hz
  exact this.elim
