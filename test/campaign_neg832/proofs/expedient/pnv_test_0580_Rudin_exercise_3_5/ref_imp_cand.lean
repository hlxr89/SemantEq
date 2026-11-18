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
  exfalso
  let a : ℕ → EReal := fun n => ((n : ℝ) : EReal)
  let b : ℕ → EReal := fun n => ((1 - (n : ℝ) : ℝ) : EReal)
  have ha_real : ∀ n, a n ≠ ⊤ ∧ a n ≠ ⊥ := by
    intro n
    exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩
  have hb_real : ∀ n, b n ≠ ⊤ ∧ b n ≠ ⊥ := by
    intro n
    exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩
  have ha_ne : limsup a ≠ ⊤ := by
    intro h
    have hp := congrFun h (pure 0)
    have hlim : limsup a (pure 0) = a 0 :=
      Filter.Tendsto.limsup_eq (tendsto_pure_left.2 fun _ hs => mem_of_mem_nhds hs)
    rw [hlim] at hp
    simp [a] at hp
  have hb_ne : limsup b ≠ ⊥ := by
    intro h
    have hp := congrFun h (pure 0)
    have hlim : limsup b (pure 0) = b 0 :=
      Filter.Tendsto.limsup_eq (tendsto_pure_left.2 fun _ hs => mem_of_mem_nhds hs)
    rw [hlim] at hp
    exact EReal.coe_ne_bot (1 : ℝ) (by simpa [b] using hp)
  have htop : limsup a atTop = ⊤ := by
    apply Filter.Tendsto.limsup_eq
    exact EReal.tendsto_coe_nhds_top_iff.2 tendsto_natCast_atTop_atTop
  have hrealbot : Tendsto (fun n : ℕ => (1 - (n : ℝ) : ℝ)) atTop atBot := by
    rw [tendsto_atBot]
    intro C
    obtain ⟨n, hn⟩ := exists_nat_gt (1 - C)
    filter_upwards [eventually_ge_atTop n] with m hm
    have hnm : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hbot : limsup b atTop = ⊥ := by
    apply Filter.Tendsto.limsup_eq
    exact EReal.tendsto_coe_nhds_bot_iff.2 hrealbot
  have h := exercise_3_5_assumed a b ha_real hb_real ha_ne hb_ne atTop
  change limsup (fun n => a n + b n) atTop ≤ limsup a atTop + limsup b atTop at h
  rw [htop, hbot] at h
  have hsum : limsup (fun n => a n + b n) atTop = (1 : EReal) := by
    have hfun : (fun n => a n + b n) = fun _ : ℕ => (1 : EReal) := by
      funext n
      change ((n : ℝ) : EReal) + ((1 - (n : ℝ) : ℝ) : EReal) = ((1 : ℝ) : EReal)
      rw [← EReal.coe_add]
      congr
      ring
    rw [hfun, limsup_const]
  rw [hsum] at h
  have h' : (1 : EReal) ≤ ⊥ := by simpa using h
  exact (not_le_of_gt (EReal.bot_lt_coe (1 : ℝ))) h'
