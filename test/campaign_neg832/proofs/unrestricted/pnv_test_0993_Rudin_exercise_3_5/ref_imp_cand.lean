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
  let u : ℕ → EReal := fun n => ((-(n : ℝ) : ℝ) : EReal)
  let v : ℕ → EReal := fun n => (((n : ℝ) : ℝ) : EReal)
  have hu : Tendsto u atTop (𝓝 ⊥) :=
    EReal.tendsto_coe_nhds_bot_iff.mpr
      (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  have hv : Tendsto v atTop (𝓝 ⊤) :=
    EReal.tendsto_coe_nhds_top_iff.mpr tendsto_natCast_atTop_atTop
  have hlu : limsup u atTop = ⊥ := hu.limsup_eq
  have hlv : limsup v atTop = ⊤ := hv.limsup_eq
  have hfalse := exercise_3_5_assumed u v
    (fun n => ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩)
    (fun n => ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩)
    (by
      intro h
      have h' := congrFun h atTop
      rw [hlu] at h'
      exact bot_ne_top h')
    (by
      intro h
      have h' := congrFun h atTop
      rw [hlv] at h'
      exact top_ne_bot h')
  have huv : (fun n => u n + v n) = fun _ => (0 : EReal) := by
    funext n
    dsimp [u, v]
    change ((-(n : ℝ) : ℝ) : EReal) + ((n : ℝ) : EReal) = 0
    rw [← EReal.coe_add]
    simp
  have : (0 : EReal) ≤ ⊥ := by
    have hfalse_atTop := hfalse atTop
    rw [huv] at hfalse_atTop
    change limsup (fun _ : ℕ => (0 : EReal)) atTop ≤
      limsup u atTop + limsup v atTop at hfalse_atTop
    rw [hlu, hlv] at hfalse_atTop
    simpa using hfalse_atTop
  exact (not_le_of_gt EReal.bot_lt_zero this).elim
