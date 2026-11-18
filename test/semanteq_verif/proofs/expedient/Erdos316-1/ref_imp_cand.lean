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
  rcases h ∅ (by simp) (by simp) (by norm_num) with ⟨A₁, A₂, _, hu, hs⟩
  have hA₁ : A₁ = ∅ := by
    ext n
    constructor
    · intro hn
      have hempty : n ∈ (∅ : Finset ℕ) := by
        rw [hu]
        exact Finset.mem_union_left A₂ hn
      simpa using hempty
    · simp
  have hA₂ : A₂ = ∅ := by
    ext n
    constructor
    · intro hn
      have hempty : n ∈ (∅ : Finset ℕ) := by
        rw [hu]
        exact Finset.mem_union_right A₁ hn
      simpa using hempty
    · simp
  subst A₁
  subst A₂
  norm_num at hs

end Erdos316
