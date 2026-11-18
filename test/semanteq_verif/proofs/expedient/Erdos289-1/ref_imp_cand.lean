import Mathlib

open Asymptotics Filter Finset

-- ===== unified context (both sides' local defs, merged) =====
-- empty

namespace Erdos289

-- ===== assumed statement (antecedent) =====
theorem erdos_289_assumed :
    (∀ᶠ k : ℕ in atTop, ∃ I : Fin k → ℕ × ℕ,
    (∀ i, (I i).1 < (I i).2) ∧
    (∀ i j, i ≠ j → (I i).2 + 1 < (I j).1 ∨ (I j).2 + 1 < (I i).1) ∧
    ∑ i, ∑ n ∈ .Icc (I i).1 (I i).2, (n⁻¹ : ℚ) = 1) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_289 : 
    (∀ᶠ k : ℕ in atTop, ∃ I : Fin k → ℕ × ℕ,
    (∀ i, (I i).1 < (I i).2) ∧
    (∀ i j, i ≠ j → (I i).2 < (I j).1 ∨ (I j).2 < (I i).1) ∧
    ∑ i, ∑ n ∈ .Icc (I i).1 (I i).2, (n⁻¹ : ℚ) = 1) := by
  filter_upwards [erdos_289_assumed] with k h
  obtain ⟨I, hlen, hsep, hsum⟩ := h
  refine ⟨I, hlen, ?_, hsum⟩
  intro i j hij
  specialize hsep i j hij
  omega

end Erdos289
