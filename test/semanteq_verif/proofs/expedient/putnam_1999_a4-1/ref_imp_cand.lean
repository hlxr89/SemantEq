import Mathlib

open Filter Topology Metric

-- ===== unified context (both sides' local defs, merged) =====
noncomputable abbrev putnam_1999_a4_solution : ℝ := 9/32

-- ===== assumed statement (antecedent) =====
theorem putnam_1999_a4_assumed
: Tendsto (fun i => ∑ m ∈ Finset.range i, ∑' n : ℕ, (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ)) atTop (𝓝 putnam_1999_a4_solution) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement : 
  ∑' m : ℕ, ∑' n : ℕ, (if m = 0 ∨ n = 0 then 0 else (m^2 * n : ℝ) / (3^m * (n * 3^m + m * 3^n))) = 9/32 := by
  let A : ℕ → ℝ := fun m =>
    ∑' n : ℕ, (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ)
  let F : ℕ → ℝ := fun m =>
    ∑' n : ℕ, (if m = 0 ∨ n = 0 then 0 else (m^2 * n : ℝ) / (3^m * (n * 3^m + m * 3^n)))
  have hA0 : ∀ m, 0 ≤ A m := by
    intro m
    exact tsum_nonneg fun n => by positivity
  have hAs : HasSum A (9 / 32 : ℝ) := by
    apply (hasSum_iff_tendsto_nat_of_nonneg hA0 _).2
    simpa [A, putnam_1999_a4_solution] using putnam_1999_a4_assumed
  have hshift : (fun m => F (m + 1)) = A := by
    funext m
    simp only [F, A, Nat.add_eq_zero_iff, one_ne_zero, and_false, false_or,
      Nat.cast_add, Nat.cast_one]
    let B : ℕ → ℝ := fun n =>
      if n = 0 then 0 else
        (↑m + 1) ^ 2 * ↑n /
          (3 ^ (m + 1) * (↑n * 3 ^ (m + 1) + (↑m + 1) * 3 ^ n))
    change (∑' n, B n) = _
    calc
      (∑' n, B n) = ∑' n, B (Nat.succ n) :=
        (Nat.succ_injective.tsum_eq (f := B) (by
          intro n hn
          have hn0 : n ≠ 0 := by
            intro h
            subst n
            simp [B] at hn
          exact ⟨n.pred, Nat.succ_pred hn0⟩)).symm
      _ = _ := by simp [B, Nat.cast_succ]
  have hFs : HasSum F (9 / 32 : ℝ) := by
    have h := (hasSum_nat_add_iff (f := F) 1).1 (by
      simpa only [hshift] using hAs)
    simpa [F] using h
  exact hFs.tsum_eq

