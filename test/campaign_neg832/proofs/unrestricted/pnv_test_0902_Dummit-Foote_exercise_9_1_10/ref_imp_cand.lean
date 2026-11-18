import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_9_1_10_assumed {f : ℕ → MvPolynomial ℕ ℤ}
  (hf : f = λ i => MvPolynomial.X (2*i) * MvPolynomial.X (2*i+1)):
  Infinite (minimalPrimes (MvPolynomial ℕ ℤ ⧸ span (range f))) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy : (Infinite (Set.range (fun (n : ℕ) => Ico (n*2) (n*2 + 1)))) := by
  let g : ℕ → Set.range (fun (n : ℕ) => Ico (n*2) (n*2 + 1)) :=
    fun n => ⟨Ico (n*2) (n*2 + 1), ⟨n, rfl⟩⟩
  exact Infinite.of_injective g (by
    intro n m h
    have hsets : Ico (n*2) (n*2 + 1) = Ico (m*2) (m*2 + 1) :=
      Subtype.ext_iff.mp h
    have hn : n*2 ∈ Ico (n*2) (n*2 + 1) := by simp
    rw [hsets] at hn
    simp only [mem_Ico] at hn
    omega)
