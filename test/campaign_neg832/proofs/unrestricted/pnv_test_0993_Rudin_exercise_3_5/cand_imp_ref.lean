import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a b : ℕ → ℝ} (ha : BddAbove (Set.range a)) (hb : BddAbove (Set.range b)): limsup (fun n => a n + b n) ≤ limsup a + limsup b := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_5
    (a b : ℕ → EReal)
    (hareal : ∀ n, a n ≠ ⊤ ∧ a n ≠ ⊥)
    (hbreal : ∀ n, b n ≠ ⊤ ∧ b n ≠ ⊥)
    (ha : limsup a ≠ ⊤)
    (hb : limsup b ≠ ⊥) :
    limsup (λ n => a n + b n) ≤ limsup a + limsup b := by
  let u : ℕ → ℝ := fun n => -(n : ℝ)
  let v : ℕ → ℝ := fun _ => -1
  have hu_bdd : BddAbove (Set.range u) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    simp [u]
  have hv_bdd : BddAbove (Set.range v) := by
    refine ⟨-1, ?_⟩
    rintro _ ⟨n, rfl⟩
    simp [v]
  have limsup_eq_zero_of_tendsto_atBot
      (w : ℕ → ℝ) (hw : Tendsto w atTop atBot) : limsup w atTop = 0 := by
    rw [Filter.limsup_eq]
    have hs : {c : ℝ | ∀ᶠ n in atTop, w n ≤ c} = Set.univ := by
      apply Set.eq_univ_of_forall
      intro c
      exact hw.eventually (Iic_mem_atBot c)
    rw [hs]
    exact Real.sInf_univ
  have hu_tendsto : Tendsto u atTop atBot := by
    change Tendsto (fun n : ℕ => -(n : ℝ)) atTop atBot
    exact tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have huv_tendsto : Tendsto (fun n => u n + v n) atTop atBot := by
    rw [tendsto_atBot] at hu_tendsto ⊢
    intro c
    filter_upwards [hu_tendsto (c + 1)] with n hn
    dsimp [v]
    linarith
  have hbad := dummy_assumed hu_bdd hv_bdd
  have hbad_atTop := hbad atTop
  change limsup (fun n => u n + v n) atTop ≤
    limsup u atTop + limsup v atTop at hbad_atTop
  rw [limsup_eq_zero_of_tendsto_atBot _ huv_tendsto,
    limsup_eq_zero_of_tendsto_atBot _ hu_tendsto, limsup_const] at hbad_atTop
  norm_num at hbad_atTop
