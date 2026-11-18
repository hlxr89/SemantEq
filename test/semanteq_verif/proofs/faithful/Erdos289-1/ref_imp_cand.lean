import Mathlib

open Asymptotics Filter Finset

namespace Erdos289

-- ===== unified context (both sides' local defs, merged) =====
-- empty

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
  filter_upwards [erdos_289_assumed] with k hk
  rcases hk with ⟨I, hlt, hsep, hsum⟩
  refine ⟨I, hlt, ?_, hsum⟩
  intro i j hij
  rcases hsep i j hij with hij' | hji'
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

end Erdos289
