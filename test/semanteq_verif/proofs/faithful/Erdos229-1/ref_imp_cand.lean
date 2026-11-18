import Mathlib

namespace Erdos229

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem erdos_229_assumed :
    letI := Polynomial.algebraPi ℂ ℂ ℂ
    ∀ (S : ℕ → Set ℂ), (∀ n, derivedSet (S n) = ∅) →
    ∃ (f : ℂ → ℂ), Transcendental (Polynomial ℂ) f ∧ Differentiable ℂ f ∧ ∀ n ≥ 1,
      ∃ k, ∀ z ∈ S n, iteratedDeriv k f z = 0 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_229_goal (S : ℕ → Set ℂ)
    (h : ∀ (n), derivedSet (S n) = ∅) :
    ∃ (f : ℂ → ℂ) (k : ℕ → ℕ), (∃ x y, f x ≠ f y) ∧ Differentiable ℂ f ∧ ∀ (n) (z) (_ : z ∈ S n),
      iteratedDeriv (k n) f z = 0 := by
  letI := Polynomial.algebraPi ℂ ℂ ℂ
  let T : ℕ → Set ℂ := fun n => S (n - 1)
  have hT : ∀ n, derivedSet (T n) = ∅ := fun n => h (n - 1)
  obtain ⟨f, hf_trans, hf_diff, hf⟩ := erdos_229_assumed T hT
  have hall : ∀ n, ∃ k, ∀ z ∈ S n, iteratedDeriv k f z = 0 := by
    intro n
    simpa [T] using hf (n + 1) (by omega)
  choose k hk using hall
  refine ⟨f, k, ?_, hf_diff, hk⟩
  have hnotconst : ¬ ∀ x y, f x = f y := by
    intro hconst
    have hp_eval : Polynomial.aeval f
        (Polynomial.X - Polynomial.C (Polynomial.C (f 0)) : Polynomial (Polynomial ℂ)) = 0 := by
      ext z
      simp [hconst z 0]
    have hp_zero := (transcendental_iff.mp hf_trans)
      (Polynomial.X - Polynomial.C (Polynomial.C (f 0))) hp_eval
    have hp_ne : Polynomial.X - Polynomial.C (Polynomial.C (f 0)) ≠
        (0 : Polynomial (Polynomial ℂ)) := by
      exact Polynomial.X_sub_C_ne_zero (Polynomial.C (f 0))
    exact hp_ne hp_zero
  push_neg at hnotconst
  exact hnotconst

end Erdos229
