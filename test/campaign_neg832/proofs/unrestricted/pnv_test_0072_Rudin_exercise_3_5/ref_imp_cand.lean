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
  let u : ℕ → EReal := fun n => (n : EReal)
  let v : ℕ → EReal := fun n => ((1 : ℝ) - n : EReal)
  have hu_real : ∀ n, u n ≠ ⊤ ∧ u n ≠ ⊥ := by
    intro n
    exact ⟨EReal.coe_ne_top n, EReal.coe_ne_bot n⟩
  have hv_real : ∀ n, v n ≠ ⊤ ∧ v n ≠ ⊥ := by
    intro n
    exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩
  have hu : limsup u ≠ (⊤ : Filter ℕ → EReal) := by
    intro h
    have hh := congrFun h ⊥
    simp at hh
  have hv : limsup v ≠ (⊥ : Filter ℕ → EReal) := by
    intro h
    have hh := congrFun h ⊤
    simp [v] at hh
    have h0 := hh 0
    apply EReal.coe_ne_bot 1
    simpa using h0
  have h := exercise_3_5_assumed u v hu_real hv_real hu hv atTop
  change limsup (fun n => u n + v n) atTop ≤ limsup u atTop + limsup v atTop at h
  have hpos : limsup u atTop = ⊤ := by
    exact (EReal.tendsto_coe_atTop.comp tendsto_natCast_atTop_atTop).limsup_eq
  have hneg : limsup v atTop = ⊥ := by
    apply Filter.Tendsto.limsup_eq
    apply EReal.tendsto_coe_atBot.comp
    rw [tendsto_atBot]
    intro x
    obtain ⟨N, hN⟩ := exists_nat_ge (1 - x)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hcast : (N : ℝ) ≤ n := Nat.cast_le.2 hn
    linarith
  have huv : (fun n => u n + v n) = (fun _ : ℕ => (1 : EReal)) := by
    funext n
    change (↑(n : ℝ) : EReal) + ↑((1 : ℝ) - n) = ↑(1 : ℝ)
    rw [← EReal.coe_add]
    congr
    norm_num
  rw [huv, Filter.limsup_const 1, hpos, hneg] at h
  norm_num at h
  exact EReal.coe_ne_bot 1 h
