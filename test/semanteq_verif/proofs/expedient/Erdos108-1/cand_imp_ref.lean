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
  obtain ⟨f, hf⟩ := erdos_108_assumed (V := Empty) 4 (by norm_num) 2 (by norm_num)
  have hzero : SimpleGraph.chromaticNumber (⊥ : SimpleGraph Empty) = 0 := by
    rw [SimpleGraph.chromaticNumber]
    simp
    infer_instance
  obtain ⟨H, _, hk⟩ := hf ⊥ (by simp [hzero])
  have hzero' : SimpleGraph.chromaticNumber H.coe = 0 := by
    have hvis : H.verts = ∅ := by
      ext x
      exact Empty.elim x
    simp [SimpleGraph.chromaticNumber, hvis]
  simp [hzero'] at hk

end Erdos108
