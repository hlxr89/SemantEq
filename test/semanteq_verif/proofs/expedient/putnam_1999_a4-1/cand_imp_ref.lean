import Mathlib

open Filter Topology Metric

-- ===== unified context (both sides' local defs, merged) =====
noncomputable abbrev putnam_1999_a4_solution : ℝ := 9/32

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed : 
  ∑' m : ℕ, ∑' n : ℕ, (if m = 0 ∨ n = 0 then 0 else (m^2 * n : ℝ) / (3^m * (n * 3^m + m * 3^n))) = 9/32 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1999_a4
: Tendsto (fun i => ∑ m ∈ Finset.range i, ∑' n : ℕ, (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ)) atTop (𝓝 putnam_1999_a4_solution) := by
  let A : ℕ → ℝ := fun m =>
    ∑' n : ℕ, (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ)
  let F : ℕ → ℝ := fun m =>
    ∑' n : ℕ, (if m = 0 ∨ n = 0 then 0 else (m^2 * n : ℝ) / (3^m * (n * 3^m + m * 3^n)))
  have hFt : ∑' m, F m = (9 / 32 : ℝ) := by
    simpa only [F] using problem_statement_assumed
  have hFsum : Summable F := by
    by_contra h
    have hz : ∑' m, F m = 0 := tsum_eq_zero_of_not_summable h
    rw [hFt] at hz
    norm_num at hz
  have hFs : HasSum F (9 / 32 : ℝ) := by
    rw [← hFt]
    exact hFsum.hasSum
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
  have hAs : HasSum A (9 / 32 : ℝ) := by
    rw [← hshift]
    apply (hasSum_nat_add_iff (f := F) 1).2
    simpa [F] using hFs
  simpa [A, putnam_1999_a4_solution] using hAs.tendsto_sum_nat
