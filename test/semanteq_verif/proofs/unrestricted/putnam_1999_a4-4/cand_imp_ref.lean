import Mathlib

open Filter Topology Metric

-- ===== unified context (both sides' local defs, merged) =====
noncomputable abbrev putnam_1999_a4_solution : ℝ := 9/32

noncomputable def term (m n : ℕ) : ℝ :=
  if m = 0 ∨ n = 0 then 0 else ((m : ℝ)^2 * (n : ℝ)) / (((3 : ℝ)^m) * ((n : ℝ) * (3 : ℝ)^m + (m : ℝ) * (3 : ℝ)^n))

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed : 
  ∑' m : ℕ, ∑' n : ℕ, term m n = 9/32 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1999_a4
: Tendsto (fun i => ∑ m ∈ Finset.range i, ∑' n : ℕ, (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ)) atTop (𝓝 putnam_1999_a4_solution) := by
  let f : ℕ → ℝ := fun m => ∑' n : ℕ,
    (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ)
  have hinner (m : ℕ) : (∑' n : ℕ, term (m + 1) n) = f m := by
    rw [← Function.Injective.tsum_eq (g := Nat.succ) Nat.succ_injective]
    · apply tsum_congr
      intro n
      simp [term, f, Nat.succ_eq_add_one]
    · intro n hn
      cases n with
      | zero => simp [term] at hn
      | succ k => exact ⟨k, rfl⟩
  have hsum : (∑' m : ℕ, f m) = 9 / 32 := by
    calc
      ∑' m : ℕ, f m = ∑' m : ℕ, ∑' n : ℕ, term (m + 1) n := by
        apply tsum_congr
        intro m
        exact (hinner m).symm
      _ = ∑' m : ℕ, ∑' n : ℕ, term m n := by
        apply Function.Injective.tsum_eq (f := fun m : ℕ => ∑' n : ℕ, term m n)
          (g := Nat.succ) Nat.succ_injective
        intro m hm
        cases m with
        | zero => simp [term] at hm
        | succ k => exact ⟨k, rfl⟩
      _ = 9 / 32 := problem_statement_assumed
  have hf : Summable f := by
    by_contra h
    have hz : (∑' m : ℕ, f m) = 0 := tsum_eq_zero_of_not_summable h
    rw [hz] at hsum
    norm_num at hsum
  have ht := hf.hasSum.tendsto_sum_nat
  rw [show putnam_1999_a4_solution = (9 / 32 : ℝ) by rfl, ← hsum]
  simpa [f] using ht
