import Mathlib

open Filter Topology Metric

-- ===== unified context (both sides' local defs, merged) =====
noncomputable abbrev putnam_1999_a4_solution : ℝ := 9/32

noncomputable def term (m n : ℕ) : ℝ :=
  if m = 0 ∨ n = 0 then 0 else ((m : ℝ)^2 * (n : ℝ)) / (((3 : ℝ)^m) * ((n : ℝ) * (3 : ℝ)^m + (m : ℝ) * (3 : ℝ)^n))

-- ===== assumed statement (antecedent) =====
theorem putnam_1999_a4_assumed
: Tendsto (fun i => ∑ m ∈ Finset.range i, ∑' n : ℕ, (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ)) atTop (𝓝 putnam_1999_a4_solution) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement : 
  ∑' m : ℕ, ∑' n : ℕ, term m n = 9/32 := by
  have tsum_shift (f : ℕ → ℝ) (hzero : f 0 = 0) :
      (∑' n : ℕ, f n) = ∑' n : ℕ, f (n + 1) := by
    apply tsum_eq_tsum_of_ne_zero_bij (fun x => x.1 + 1)
    · intro x y hxy
      apply Subtype.ext
      exact Nat.add_right_cancel hxy
    · intro n hn
      have hn0 : n ≠ 0 := by
        intro hnz
        subst n
        exact hn hzero
      have hone : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      refine ⟨⟨n - 1, ?_⟩, ?_⟩
      · change f ((n - 1) + 1) ≠ 0
        simpa [Nat.sub_add_cancel hone] using hn
      · simp [Nat.sub_add_cancel hone]
    · intro x
      rfl
  let a : ℕ → ℝ := fun m =>
    ∑' n : ℕ, (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ)
  have hterm (m n : ℕ) :
      term (m + 1) (n + 1) =
        (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ) := by
    simp [term]
  have hinner (m : ℕ) : (∑' n : ℕ, term (m + 1) n) = a m := by
    rw [tsum_shift (fun n => term (m + 1) n) (by simp [term])]
    exact tsum_congr (hterm m)
  have hbridge : (∑' m : ℕ, ∑' n : ℕ, term m n) = ∑' m : ℕ, a m := by
    rw [tsum_shift (fun m => ∑' n : ℕ, term m n) (by simp [term])]
    exact tsum_congr hinner
  have hnonneg (m : ℕ) : 0 ≤ a m := by
    apply tsum_nonneg
    intro n
    dsimp [a]
    positivity
  have hsum : HasSum a putnam_1999_a4_solution :=
    (hasSum_iff_tendsto_nat_of_nonneg hnonneg putnam_1999_a4_solution).2
      putnam_1999_a4_assumed
  rw [hbridge, hsum.tsum_eq]
