import Mathlib

open Cardinal Filter

open scoped Pointwise Topology

namespace Erdos949

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem erdos_949_assumed : ∀ᵉ (S : Set ℝ), (∀ᵉ (a ∈ S) (b ∈ S), ¬ a + b ∈ S) →
    ∃ (A : Set ℝ), A ⊆ Set.univ \ S ∧
    Cardinal.mk A = Cardinal.continuum ∧ A + A ⊆ A := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_949_goal :
    ∀ S : Set ℝ, (∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) → ∃ A ⊆ Sᶜ, #A = 𝔠 ∧ A + A ⊆ Sᶜ := by
  intro S hS
  obtain ⟨A, hAS, hcard, hadd⟩ := erdos_949_assumed S hS
  rw [Set.compl_eq_univ_diff]
  exact ⟨A, hAS, hcard, fun _ hx => hAS (hadd hx)⟩

end Erdos949
