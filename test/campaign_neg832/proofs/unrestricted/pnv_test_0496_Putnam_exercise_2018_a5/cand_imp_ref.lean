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
  let g : ℝ → ℝ := fun x => x ^ 2
  have hg : ContDiff ℝ ⊤ g := by
    fun_prop
  have hg0 : g 0 = 0 := by
    norm_num [g]
  have hg1 : g 1 = 1 := by
    norm_num [g]
  have hg_pos : ∀ x, 0 ≤ g x := by
    intro x
    exact sq_nonneg x
  have hg_inj : Set.InjOn g (Set.Icc 0 1) := by
    intro x hx y hy hxy
    dsimp [g] at hxy
    apply (mul_self_inj_of_nonneg hx.1 hy.1).mp
    simpa [pow_two] using hxy
  obtain ⟨n, x, hx, hderiv, hneg⟩ :=
    dummy_assumed hg hg0 hg1 hg_pos hg_inj
  have hnonneg : 0 ≤ (g^[n+1]) x := by
    rw [Function.iterate_succ_apply']
    exact hg_pos ((g^[n]) x)
  exact (not_lt_of_ge hnonneg hneg).elim
