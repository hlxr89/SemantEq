import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_43_2_assumed {X : Type*} [MetricSpace X]
  {Y : Type*} [MetricSpace Y] [CompleteSpace Y] (A : Set X)
  (f : X → Y) (hf : UniformContinuousOn f A) :
  ∃! (g : X → Y), ContinuousOn g (closure A) ∧
  UniformContinuousOn g (closure A) ∧ ∀ (x : A), g x = f x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {X Y : Type*} [MetricSpace X] [MetricSpace Y] (hY : CompleteSpace Y) {f : X → Y} {A : Set X} (hA : IsCompact A) (hf : UniformContinuousOn f A) : ∃ g : X → Y, Continuous g ∧ UniformContinuous g ∧ EqOn f g A := by
  classical
  letI : CompleteSpace Y := hY
  obtain ⟨g, hg, huniq⟩ := exercise_43_2_assumed A f hf
  have hclosure : closure A = A := hA.isClosed.closure_eq
  by_cases hAX : A = (Set.univ : Set X)
  · refine ⟨g, ?_, ?_, ?_⟩
    · exact continuousOn_univ.mp (hAX ▸ (hclosure ▸ hg.1))
    · exact uniformContinuousOn_univ.mp (hAX ▸ (hclosure ▸ hg.2.1))
    · intro x hx
      exact (hg.2.2 ⟨x, hx⟩).symm
  · obtain ⟨x₀, hx₀⟩ : ∃ x, x ∉ A := by
      simpa [Set.eq_univ_iff_forall] using hAX
    have hsub : Subsingleton Y := by
      constructor
      intro y₁ y₂
      have hy (y : Y) : y = g x₀ := by
        let gy : X → Y := Function.update g x₀ y
        have heq : EqOn gy g (closure A) := by
          intro x hx
          have hxA : x ∈ A := hclosure ▸ hx
          have hne : x ≠ x₀ := by
            intro h
            exact hx₀ (h ▸ hxA)
          simp [gy, hne]
        have hgy : ContinuousOn gy (closure A) ∧
            UniformContinuousOn gy (closure A) ∧ ∀ (x : A), gy x = f x := by
          refine ⟨hg.1.congr heq, hg.2.1.congr heq.symm, ?_⟩
          intro x
          rw [heq (x := (x : X)) (by simpa [hclosure] using x.property)]
          exact hg.2.2 x
        have he := congrFun (huniq gy hgy) x₀
        simpa [gy] using he
      exact (hy y₁).trans (hy y₂).symm
    letI : Subsingleton Y := hsub
    have hconst : g = fun _ => f x₀ := by
      funext x
      exact Subsingleton.elim _ _
    refine ⟨g, ?_, ?_, ?_⟩
    · rw [hconst]
      exact continuous_const
    · rw [hconst]
      exact uniformContinuous_const
    · intro x hx
      exact (hg.2.2 ⟨x, hx⟩).symm
