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
  have hn : Tendsto (fun n : ℕ => -(n : ℝ)) atTop atBot :=
    tendsto_neg_atBot_iff.mpr tendsto_natCast_atTop_atTop
  have hnc : ¬IsCoboundedUnder (· ≤ ·) atTop (fun n : ℕ => -(n : ℝ)) := by
    intro h
    rcases h with ⟨c, hc⟩
    have hc' := hc (c - 1)
    simp only [eventually_map] at hc'
    exact (not_le_of_gt (sub_lt_self c zero_lt_one)) (hc' ((tendsto_atBot.1 hn) (c - 1)))
  have hns : ¬IsCoboundedUnder (· ≤ ·) atTop (fun n : ℕ => -(n : ℝ) + (-1)) := by
    intro h
    rcases h with ⟨c, hc⟩
    have hc' := hc (c - 1)
    simp only [eventually_map] at hc'
    have ht : Tendsto (fun n : ℕ => -(n : ℝ) + (-1)) atTop atBot := by
      refine tendsto_atBot.2 fun c => ?_
      filter_upwards [(tendsto_atBot.1 hn) (c + 1)] with n hn'
      linarith
    exact (not_le_of_gt (sub_lt_self c zero_lt_one)) (hc' ((tendsto_atBot.1 ht) (c - 1)))
  have h := dummy_assumed
    (a := fun n : ℕ => -(n : ℝ)) (b := fun _ : ℕ => -1)
    (by
      refine ⟨0, ?_⟩
      rintro _ ⟨n, rfl⟩
      exact neg_nonpos.mpr (Nat.cast_nonneg n))
    (by refine ⟨-1, ?_⟩; rintro _ ⟨n, rfl⟩; simp)
  have : False := by
    have h := h atTop
    change Filter.limsup (fun n : ℕ => -(n : ℝ) + (-1)) atTop ≤
      Filter.limsup (fun n : ℕ => -(n : ℝ)) atTop +
        Filter.limsup (fun _ : ℕ => (-1 : ℝ)) atTop at h
    rw [Real.limsup_of_not_isCoboundedUnder hns,
      Real.limsup_of_not_isCoboundedUnder hnc, limsup_const] at h
    norm_num at h
  exact this.elim
