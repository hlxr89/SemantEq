import Mathlib

open Cardinal Filter

open scoped Pointwise Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

namespace Erdos949

-- ===== assumed statement (antecedent) =====
theorem erdos_949_assumed : ∀ᵉ (S : Set ℝ), (∀ᵉ (a ∈ S) (b ∈ S), ¬ a + b ∈ S) →
    ∃ (A : Set ℝ), A ⊆ Set.univ \ S ∧
    Cardinal.mk A = Cardinal.continuum ∧ A + A ⊆ A := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_949_goal :
    ∀ S : Set ℝ, (∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) → ∃ A ⊆ Sᶜ, #A = 𝔠 ∧ A + A ⊆ Sᶜ := by
  intro S hS
  obtain ⟨A, hA, hcard, hadd⟩ := erdos_949_assumed S hS
  refine ⟨A, ?_, hcard, ?_⟩
  · intro x hx
    exact (hA hx).2
  · intro x hx
    exact (hA (hadd hx)).2

end Erdos949
