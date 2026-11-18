import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

universe u

namespace Erdos108

-- ===== assumed statement (antecedent) =====
theorem erdos_108_assumed {V : Type u} :
    ∀ r ≥ 4, ∀ k ≥ 2, ∃ (f : ℕ),
    ∀ (G : SimpleGraph V) (hchro : SimpleGraph.chromaticNumber G ≤ f),
    ∃ (H : G.Subgraph), (SimpleGraph.girth H.coe ≥ r) ∧
    (SimpleGraph.chromaticNumber H.coe ≥ k) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_108_goal :
    ∀ r ≥ 4, ∀ k ≥ (2 : ℕ), ∃ (f : ℕ),
    ∀ (V : Type u) (G : SimpleGraph V) (_ : Nonempty V)
      (hchro : f ≤ SimpleGraph.chromaticNumber G),
    ∃ (H : G.Subgraph), (SimpleGraph.girth H.coe ≥ r) ∧
    (SimpleGraph.chromaticNumber H.coe ≥ k) := by
  exfalso
  obtain ⟨f, hf⟩ := erdos_108_assumed (V := Empty) 4 le_rfl 2 le_rfl
  obtain ⟨H, _, hchrom⟩ := hf ⊥ (by
    rw [SimpleGraph.chromaticNumber_eq_zero_of_isEmpty]
    exact bot_le)
  rw [SimpleGraph.chromaticNumber_eq_zero_of_isEmpty] at hchrom
  exact (by simpa using hchrom)

end Erdos108
