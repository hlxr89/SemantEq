import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} [Fact (Nat.Prime p)] (f : Polynomial (ZMod p)) (hf : f.Monic) (hfd : f.degree > 1) (hp : ∀ (x : ℕ), x < p → p ∣ x^p - x) : Irreducible f := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_4_2a : Irreducible (X^4 - 4*X^3 + 6 : Polynomial ℤ) := by
  let f : Polynomial ℤ := X^4 - 4*X^3 + 6
  let P : Ideal ℤ := Ideal.span {(2 : ℤ)}
  have hf : f.Monic := by
    dsimp [f]
    monicity <;> norm_num
  have hdeg : f.natDegree = 4 := by
    dsimp [f]
    compute_degree <;> norm_num
  have hP : P.IsPrime := by
    dsimp [P]
    rw [Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)]
    norm_num
  have he : f.IsEisensteinAt P := by
    refine hf.isEisensteinAt_of_mem_of_notMem hP.ne_top ?_ ?_
    · intro n hn
      rw [hdeg] at hn
      dsimp [P]
      rw [Ideal.mem_span_singleton]
      interval_cases n <;> simp [f]
    · dsimp [P]
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      norm_num [f]
  change Irreducible f
  exact he.irreducible hP hf.isPrimitive (by omega)
