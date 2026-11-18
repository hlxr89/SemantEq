import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (a b : ℕ → ℝ) : limsup (a + b) ≤ limsup a + limsup b := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_5
    (a b : ℕ → EReal)
    (hareal : ∀ n, a n ≠ ⊤ ∧ a n ≠ ⊥)
    (hbreal : ∀ n, b n ≠ ⊤ ∧ b n ≠ ⊥)
    (ha : limsup a ≠ ⊤)
    (hb : limsup b ≠ ⊥) :
    limsup (λ n => a n + b n) ≤ limsup a + limsup b := by
  exfalso
  have hneg : limsup (fun n : ℕ => -(n : ℝ)) atTop = 0 := by
    rw [Filter.limsup_eq]
    rw [show {x : ℝ | ∀ᶠ n : ℕ in atTop, -(n : ℝ) ≤ x} = Set.univ by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      have hx : ∀ᶠ n : ℕ in atTop, -x ≤ (n : ℝ) :=
        tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (-x))
      filter_upwards [hx] with n hn
      linarith]
    exact Real.sInf_univ
  have hpos : limsup (fun n : ℕ => (n : ℝ) + 1) atTop = 0 := by
    rw [Filter.limsup_eq]
    rw [show {x : ℝ | ∀ᶠ n : ℕ in atTop, (n : ℝ) + 1 ≤ x} = ∅ by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hx
      have hx' : ∀ᶠ n : ℕ in atTop, x ≤ (n : ℝ) :=
        tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop x)
      obtain ⟨n, hn, hn'⟩ := (hx.and hx').exists
      linarith]
    exact Real.sInf_empty
  have h := dummy_assumed (fun n : ℕ => -(n : ℝ)) (fun n : ℕ => (n : ℝ) + 1) atTop
  have heq : ((fun n : ℕ => -(n : ℝ)) + fun n : ℕ => (n : ℝ) + 1) =
      fun _ : ℕ => (1 : ℝ) := by
    funext n
    simp [Pi.add_apply]
  rw [heq] at h
  change limsup (fun _ : ℕ => (1 : ℝ)) atTop ≤
    limsup (fun n : ℕ => -(n : ℝ)) atTop +
      limsup (fun n : ℕ => (n : ℝ) + 1) atTop at h
  rw [hneg, hpos] at h
  norm_num at h
