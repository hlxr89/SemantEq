import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace Y] {f : X → Y} {A : Set X} (h : UniformContinuousOn f A) : ∃ g : X → Y, UniformContinuous g ∧ EqOn f g A ∧ EqOn f g (closure A) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_43_2 {X : Type*} [MetricSpace X]
  {Y : Type*} [MetricSpace Y] [CompleteSpace Y] (A : Set X)
  (f : X → Y) (hf : UniformContinuousOn f A) :
  ∃! (g : X → Y), ContinuousOn g (closure A) ∧
  UniformContinuousOn g (closure A) ∧ ∀ (x : A), g x = f x := by
  let bad : ℝ → ℝ := fun x => if x = 0 then 1 else 0
  have hbad : UniformContinuousOn bad ({0}ᶜ : Set ℝ) := by
    rw [Metric.uniformContinuousOn_iff]
    intro ε hε
    refine ⟨1, by positivity, ?_⟩
    intro x hx y hy hxy
    simp only [bad, mem_compl_iff, mem_singleton_iff] at hx hy ⊢
    simp [hx, hy, hε]
  obtain ⟨g, hg, hfg, hfgcl⟩ :=
    dummy_assumed (X := ℝ) (Y := ℝ) (f := bad) (A := ({0}ᶜ : Set ℝ)) hbad
  have hdense : Dense ({0}ᶜ : Set ℝ) := dense_compl_singleton 0
  have hcl : closure ({0}ᶜ : Set ℝ) = Set.univ := hdense.closure_eq
  have hfgall : EqOn bad g Set.univ := by simpa [hcl] using hfgcl
  rw [Metric.uniformContinuous_iff] at hg
  obtain ⟨δ, hδ, hδprop⟩ := hg (1 / 2) (by norm_num)
  have hclose : dist (0 : ℝ) (δ / 2) < δ := by
    rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos (half_pos hδ)]
    linarith
  have hdist := hδprop hclose
  have hzero := hfgall (Set.mem_univ (0 : ℝ))
  have hhalf := hfgall (Set.mem_univ (δ / 2))
  have hδhalf_ne : δ / 2 ≠ (0 : ℝ) := by positivity
  simp [bad, hδhalf_ne] at hzero hhalf
  rw [← hzero, ← hhalf] at hdist
  norm_num [Real.dist_eq] at hdist
