import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

namespace Erdos316

-- ===== assumed statement (antecedent) =====
theorem erdos_316_assumed :
    ¬ ∀ A : Finset ℕ, 0 ∉ A → 1 ∉ A →
    ∑ n ∈ A, (1 / n : ℚ) < 2 → ∃ (A₁ A₂ : Finset ℕ),
      Disjoint A₁ A₂ ∧ A = A₁ ∪ A₂ ∧
      ∑ n ∈ A₁, (1 / n : ℚ) < 1 ∧ ∑ n ∈ A₂, (1 / n : ℚ) <  1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_316_goal :
    ¬ ∀ A : Finset ℕ, 0 ∉ A → 1 ∉ A →
    ∑ n ∈ A, (1 / n : ℚ) < 2 → ∃ (A₁ A₂ : Finset ℕ),
      Disjoint A₁ A₂ ∧ A = A₁ ∪ A₂ ∧
      (1 ≤ ∑ n ∈ A₁, (1 / n : ℚ) ∨ 1 ≤ ∑ n ∈ A₂, (1 / n : ℚ)) := by
  intro h
  specialize h ∅ (by simp) (by simp) (by norm_num)
  rcases h with ⟨A₁, A₂, _, hunion, hlarge⟩
  have hempty : A₁ = ∅ ∧ A₂ = ∅ := Finset.union_eq_empty.mp hunion.symm
  rcases hempty with ⟨rfl, rfl⟩
  norm_num at hlarge

end Erdos316
