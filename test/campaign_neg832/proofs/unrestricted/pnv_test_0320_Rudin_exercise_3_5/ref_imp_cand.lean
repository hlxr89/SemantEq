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
theorem dummy {a b : ℕ → ℝ} (ha : Tendsto (fun n => a n) atTop atTop) (hb : Tendsto (fun n => b n) atTop atTop) : Tendsto (fun n => a n + b n) atTop atTop ∧ limsup (fun n => a n + b n) ≤ limsup (fun n => a n) + limsup (fun n => b n) := by
  constructor
  · rw [tendsto_atTop]
    intro c
    filter_upwards [(tendsto_atTop.1 ha) c, (tendsto_atTop.1 hb) 0] with n han hbn
    linarith
  · intro f
    by_cases hf : f.NeBot
    · letI : f.NeBot := hf
      have transfer_bound (x y : ℕ → ℝ) (hx : Tendsto x atTop atTop)
          (hxf : f.IsBoundedUnder (· ≤ ·) x) : f.IsBoundedUnder (· ≤ ·) y := by
        obtain ⟨C, hC⟩ := hxf.eventually_le
        obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_atTop.1 hx) (C + 1))
        have hidx : ∀ᶠ n in f, n ≤ N := hC.mono fun n hn => by
          by_contra hnot
          have hlarge := hN n (Nat.le_of_not_ge hnot)
          linarith
        exact (Set.finite_Iic N).image y |>.bddAbove.isBoundedUnder hidx
      have lower_a : f.IsBoundedUnder (· ≥ ·) a :=
        (bddBelow_range_of_tendsto_atTop_atTop ha).isBoundedUnder_of_range
      have lower_b : f.IsBoundedUnder (· ≥ ·) b :=
        (bddBelow_range_of_tendsto_atTop_atTop hb).isBoundedUnder_of_range
      by_cases upper_a : f.IsBoundedUnder (· ≤ ·) a
      · have upper_b : f.IsBoundedUnder (· ≤ ·) b := transfer_bound a b ha upper_a
        exact limsup_add_le lower_a upper_a lower_b.isCoboundedUnder_le upper_b
      · have upper_b : ¬f.IsBoundedUnder (· ≤ ·) b := fun h =>
          upper_a (transfer_bound b a hb h)
        have upper_add : ¬f.IsBoundedUnder (· ≤ ·) (fun n => a n + b n) := by
          intro hsum
          obtain ⟨S, hS⟩ := hsum.eventually_le
          obtain ⟨B, hB⟩ := lower_b.eventually_ge
          have ha_upper_event : ∀ᶠ n in f, a n ≤ S - B :=
            (hS.and hB).mono fun n hn => by linarith
          exact upper_a (isBoundedUnder_of_eventually_le ha_upper_event)
        have limsup_zero (u : ℕ → ℝ) (hu : ¬f.IsBoundedUnder (· ≤ ·) u) :
            limsup u f = 0 := by
          rw [limsup_eq]
          have hempty : {c : ℝ | ∀ᶠ n in f, u n ≤ c} = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.2
            intro c hc
            exact hu ⟨c, hc⟩
          rw [hempty]
          simp
        change limsup (fun n => a n + b n) f ≤ limsup a f + limsup b f
        rw [limsup_zero a upper_a, limsup_zero b upper_b,
          limsup_zero (fun n => a n + b n) upper_add]
        norm_num
    · rw [not_neBot] at hf
      subst f
      have limsup_bot_real (u : ℕ → ℝ) : limsup u (⊥ : Filter ℕ) = 0 := by
        rw [limsup_eq]
        simp
      change limsup (fun n => a n + b n) (⊥ : Filter ℕ) ≤
        limsup a (⊥ : Filter ℕ) + limsup b (⊥ : Filter ℕ)
      rw [limsup_bot_real, limsup_bot_real, limsup_bot_real]
      norm_num
