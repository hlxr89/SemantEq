import Mathlib

open Filter Topology Metric

-- ===== unified context (both sides' local defs, merged) =====
noncomputable abbrev putnam_1999_a4_solution : ℝ := 9/32

noncomputable def term (m n : ℕ) : ℝ :=
  if m = 0 ∨ n = 0 then 0 else ((m : ℝ)^2 * (n : ℝ)) / (((3 : ℝ)^m) * ((n : ℝ) * (3 : ℝ)^m + (m : ℝ) * (3 : ℝ)^n))

-- ===== assumed statement (antecedent) =====
theorem putnam_1999_a4_assumed
: Tendsto (fun i => ∑ m ∈ Finset.range i, ∑' n : ℕ, (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ)) atTop (𝓝 putnam_1999_a4_solution) :=
by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement : 
  ∑' m : ℕ, ∑' n : ℕ, term m n = 9/32 := by
  let f : ℕ → ℝ := fun m => ∑' n : ℕ,
    (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ)
  have hf_nonneg : ∀ m, 0 ≤ f m := by
    intro m
    apply tsum_nonneg
    intro n
    dsimp [f]
    positivity
  have hf : HasSum f (9 / 32 : ℝ) := by
    apply (hasSum_iff_tendsto_nat_of_nonneg hf_nonneg (9 / 32 : ℝ)).2
    simpa [f, putnam_1999_a4_solution] using putnam_1999_a4_assumed
  have hinner (m : ℕ) : (∑' n : ℕ, term (m + 1) n) = f m := by
    rw [← Function.Injective.tsum_eq (g := Nat.succ) Nat.succ_injective]
    · apply tsum_congr
      intro n
      simp [term, f, Nat.succ_eq_add_one]
    · intro n hn
      cases n with
      | zero => simp [term] at hn
      | succ k => exact ⟨k, rfl⟩
  calc
    ∑' m : ℕ, ∑' n : ℕ, term m n = ∑' m : ℕ, ∑' n : ℕ, term (m + 1) n := by
      symm
      apply Function.Injective.tsum_eq (f := fun m : ℕ => ∑' n : ℕ, term m n)
        (g := Nat.succ) Nat.succ_injective
      intro m hm
      cases m with
      | zero => simp [term] at hm
      | succ k => exact ⟨k, rfl⟩
    _ = ∑' m : ℕ, f m := tsum_congr hinner
    _ = 9 / 32 := hf.tsum_eq
