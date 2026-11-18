import Mathlib

open Filter

open scoped Topology Real

-- ===== unified context (both sides' local defs, merged) =====
namespace Erdos1

abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
    A ⊆ Finset.Icc 1 N ∧ (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective

-- ===== assumed statement (antecedent) =====
theorem erdos_1_assumed :
    ¬ ∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ) (_ : IsSumDistinctSet A N),
    N ≠ 0 → C * 2 ^ A.card < N := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_1_goal :
    ¬ ∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ) (_ : IsSumDistinctSet A N),
    C * 2 ^ A.card < N := by
  intro h
  apply erdos_1_assumed
  rcases h with ⟨C, hC, h⟩
  exact ⟨C, hC, fun N A hA _ => h N A hA⟩

end Erdos1
