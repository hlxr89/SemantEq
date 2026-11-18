import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) (hf0 : f 0 = 0) (hf1 : f 1 = 1) (hf_pos : ∀ x, 0 ≤ f x) (hf_inj : Set.InjOn f (Set.Icc 0 1)) : ∃ (n : ℕ) (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1), HasDerivAt (fun x => (f^[n]) x) (f^[n+1] x) x ∧ (f^[n+1] x) < 0 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2018_a5 (f : ℝ → ℝ) (hf : ContDiff ℝ ⊤ f)
  (hf0 : f 0 = 0) (hf1 : f 1 = 1) (hf2 : ∀ x, f x ≥ 0) :
  ∃ (n : ℕ+) (x : ℝ), iteratedDeriv n f x < 0 := by
  obtain ⟨n, x, hx, hderiv, hneg⟩ := dummy_assumed
    (f := fun x : ℝ => x ^ 2) (contDiff_id.pow 2) (by norm_num) (by norm_num)
    (by intro x; positivity)
    (by
      intro a ha b hb hab
      dsimp at hab
      nlinarith [ha.1, hb.1])
  have hnonneg : 0 ≤ ((fun x : ℝ => x ^ 2)^[n + 1]) x := by
    rw [show n + 1 = n.succ by omega, Function.iterate_succ_apply']
    positivity
  linarith
