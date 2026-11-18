import Mathlib

open Filter Topology Metric

-- ===== unified context (both sides' local defs, merged) =====
noncomputable abbrev putnam_1999_a4_solution : ℝ := 9/32

-- ===== assumed statement (antecedent) =====
theorem putnam_1999_a4_assumed
: Tendsto (fun i => ∑ m ∈ Finset.range i, ∑' n : ℕ, (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ)) atTop (𝓝 putnam_1999_a4_solution) :=
by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement :
  ∑' m : ℕ, ∑' n : ℕ, (m^2 * n : ℝ) / ((3^m : ℝ) * ((n * 3^m : ℝ) + (m * 3^n : ℝ))) = 9 / 32 := by
  let a : ℕ → ℕ → ℝ := fun m n =>
    (m^2 * n : ℝ) / ((3^m : ℝ) * ((n * 3^m : ℝ) + (m * 3^n : ℝ)))
  have shift_tsum (f : ℕ → ℝ) (h0 : f 0 = 0) :
      ∑' n : ℕ, f n = ∑' n : ℕ, f (n + 1) := by
    apply tsum_eq_tsum_of_ne_zero_bij
      (fun x : ↥(Function.support (fun n : ℕ => f (n + 1))) => x.1 + 1)
    · intro x y hxy
      exact Subtype.ext (Nat.add_right_cancel hxy)
    · intro x hx
      have hx0 : x ≠ 0 := by
        intro h
        subst x
        exact hx h0
      let y : ℕ := x - 1
      have hy : f (y + 1) ≠ 0 := by
        simpa [y, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hx0)] using hx
      exact ⟨⟨y, hy⟩, by simp [y, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hx0)]⟩
    · intro x
      rfl
  have hnonneg : ∀ m n, 0 ≤ a (m + 1) (n + 1) := by
    intro m n
    dsimp [a]
    positivity
  have hsum : HasSum (fun m => ∑' n : ℕ, a (m + 1) (n + 1)) (9 / 32) := by
    apply (hasSum_iff_tendsto_nat_of_nonneg (fun m => tsum_nonneg (hnonneg m)) (9 / 32)).2
    simpa [a, putnam_1999_a4_solution] using putnam_1999_a4_assumed
  calc
    ∑' m : ℕ, ∑' n : ℕ, (m^2 * n : ℝ) / ((3^m : ℝ) * ((n * 3^m : ℝ) + (m * 3^n : ℝ)))
        = ∑' m : ℕ, ∑' n : ℕ, a m n := by rfl
    _ = ∑' m : ℕ, ∑' n : ℕ, a (m + 1) (n + 1) := by
      rw [shift_tsum (fun m => ∑' n : ℕ, a m n) (by simp [a])]
      apply tsum_congr
      intro m
      exact shift_tsum (a (m + 1)) (by simp [a])
    _ = 9 / 32 := hsum.tsum_eq
