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
  classical
  let f : ℕ → MvPolynomial ℕ ℤ :=
    fun i => MvPolynomial.X (2*i) * MvPolynomial.X (2*i+1)
  letI : Infinite (minimalPrimes (MvPolynomial ℕ ℤ ⧸ span (range f))) :=
    exercise_9_1_10_assumed (f := f) rfl
  let emb := Infinite.natEmbedding
    (minimalPrimes (MvPolynomial ℕ ℤ ⧸ span (range f)))
  let code : ℕ → ℕ := fun n =>
    Classical.choose (show ∃ m, emb m = emb n from ⟨n, rfl⟩)
  have hcode (n : ℕ) : code n = n := by
    apply emb.injective
    exact Classical.choose_spec (show ∃ m, emb m = emb n from ⟨n, rfl⟩)
  let g : ℕ → Set ℕ := fun n => Ico (code n * 2) (code n * 2 + 1)
  have hg : Function.Injective g := by
    intro m n hmn
    have hm : code m * 2 ∈ g m := by simp [g]
    rw [hmn] at hm
    simp [g] at hm
    rw [hcode m, hcode n] at hm
    omega
  exact Infinite.of_injective
    (fun n => (⟨g n, Set.mem_range_self (code n)⟩ :
      Set.range (fun n : ℕ => Ico (n * 2) (n * 2 + 1))))
    (fun _ _ h => hg (Subtype.ext_iff.mp h))
