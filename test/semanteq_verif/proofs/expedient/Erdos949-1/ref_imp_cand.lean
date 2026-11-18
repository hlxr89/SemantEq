import Mathlib

open Cardinal Filter

open scoped Pointwise Topology

namespace Erdos949

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem erdos_949_assumed :
    ∀ S : Set ℝ, (∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) → ∃ A ⊆ Sᶜ, #A = 𝔠 ∧ A + A ⊆ Sᶜ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_949_goal : ∀ᵉ (S : Set ℝ), (∀ᵉ (a ∈ S) (b ∈ S), ¬ a + b ∈ S) →
    ∃ (A : Set ℝ), A ⊆ Set.univ \ S ∧
    Cardinal.mk A = Cardinal.continuum ∧ A + A ⊆ A := by
  -- not proved: the antecedent only ensures A + A ⊆ Sᶜ, not A + A ⊆ A
  sorry

end Erdos949
