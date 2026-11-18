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
  have hsum : Tendsto (fun n => a n + b n) atTop atTop :=
    tendsto_atTop_mono' atTop
      (by
        filter_upwards [hb (eventually_ge_atTop 0)] with n hn
        exact le_add_of_nonneg_right hn)
      ha
  refine ⟨hsum, ?_⟩
  intro f
  change limsup (fun n => a n + b n) f ≤ limsup a f + limsup b f
  rcases f.eq_or_neBot with rfl | hf
  · simp [Filter.limsup, Filter.limsSup]
  have hbounded (u : ℕ → ℝ) (hu : Tendsto u atTop atTop)
      (huf : f.IsBoundedUnder (· ≤ ·) u) (v : ℕ → ℝ) :
      f.IsBoundedUnder (· ≤ ·) v := by
    obtain ⟨c, hc⟩ := huf
    have hc' : ∀ᶠ n in f, u n ≤ c := by
      simpa only [eventually_map] using hc
    have hfinite : {n | u n ≤ c}.Finite := by
      simpa only [not_lt] using
        (eventually_cofinite.mp (show ∀ᶠ n in cofinite, c < u n by
          rw [Nat.cofinite_eq_atTop]
          exact hu (eventually_gt_atTop c)))
    exact (hfinite.image v).bddAbove.isBoundedUnder hc'
  have hlimsup (u : ℕ → ℝ) (hu : ¬f.IsBoundedUnder (· ≤ ·) u) :
      limsup u f = 0 := by
    rw [limsup_eq]
    have heq : {c : ℝ | ∀ᶠ n in f, u n ≤ c} = ∅ := by
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hc => hu ⟨c, by simpa only [eventually_map] using hc⟩
    rw [heq]
    simp
  by_cases hba : f.IsBoundedUnder (· ≤ ·) a
  · have habove := hbounded a ha hba b
    have hbelow_a : f.IsBoundedUnder (· ≥ ·) a := by
      obtain ⟨c, hc⟩ := hba
      have hc' : ∀ᶠ n in f, a n ≤ c := by
        simpa only [eventually_map] using hc
      have hfinite : {n | a n ≤ c}.Finite := by
        simpa only [not_lt] using
          (eventually_cofinite.mp (show ∀ᶠ n in cofinite, c < a n by
            rw [Nat.cofinite_eq_atTop]
            exact ha (eventually_gt_atTop c)))
      exact (hfinite.image a).bddBelow.isBoundedUnder hc'
    have hbelow_b : f.IsBoundedUnder (· ≥ ·) b := by
      obtain ⟨c, hc⟩ := hba
      have hc' : ∀ᶠ n in f, a n ≤ c := by
        simpa only [eventually_map] using hc
      have hfinite : {n | a n ≤ c}.Finite := by
        simpa only [not_lt] using
          (eventually_cofinite.mp (show ∀ᶠ n in cofinite, c < a n by
            rw [Nat.cofinite_eq_atTop]
            exact ha (eventually_gt_atTop c)))
      exact (hfinite.image b).bddBelow.isBoundedUnder hc'
    exact limsup_add_le hbelow_a hba hbelow_b.isCobounded_flip habove
  · have hbb : ¬f.IsBoundedUnder (· ≤ ·) b := fun h => hba (hbounded b hb h a)
    have hbs : ¬f.IsBoundedUnder (· ≤ ·) (fun n => a n + b n) :=
      fun h => hba (hbounded (fun n => a n + b n) hsum h a)
    rw [hlimsup _ hbs, hlimsup _ hba, hlimsup _ hbb]
    norm_num
