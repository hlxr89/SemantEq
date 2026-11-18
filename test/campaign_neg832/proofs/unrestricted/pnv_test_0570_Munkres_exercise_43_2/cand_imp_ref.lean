import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X Y : Type*} [MetricSpace X] [MetricSpace Y] (hY : CompleteSpace Y) {f : X → Y} {A : Set X} (hA : IsCompact A) (hf : UniformContinuousOn f A) : ∃ g : X → Y, Continuous g ∧ UniformContinuous g ∧ EqOn f g A := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_43_2 {X : Type*} [MetricSpace X]
  {Y : Type*} [MetricSpace Y] [CompleteSpace Y] (A : Set X)
  (f : X → Y) (hf : UniformContinuousOn f A) :
  ∃! (g : X → Y), ContinuousOn g (closure A) ∧
  UniformContinuousOn g (closure A) ∧ ∀ (x : A), g x = f x := by
  let fbad : ℝ → Nat := fun x => if x = 0 then 0 else 1
  have hcompact : IsCompact ({0, 1} : Set ℝ) := by
    exact Set.Finite.isCompact (by simp)
  have huniform : UniformContinuousOn fbad ({0, 1} : Set ℝ) := by
    rw [Metric.uniformContinuousOn_iff]
    intro ε hε
    refine ⟨1, by norm_num, ?_⟩
    intro x hx y hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      simp_all [fbad]
  have hext := dummy_assumed (X := ℝ) (Y := Nat)
    (inferInstance : CompleteSpace Nat) (f := fbad) (A := {0, 1}) hcompact huniform
  rcases hext with ⟨g, hg, hgu, heq⟩
  have hg0 : g 0 = 0 := by
    simpa [fbad] using (heq (by simp : (0 : ℝ) ∈ ({0, 1} : Set ℝ))).symm
  have hg1 : g 1 = 1 := by
    simpa [fbad] using (heq (by simp : (1 : ℝ) ∈ ({0, 1} : Set ℝ))).symm
  have hclopen : IsClopen (g ⁻¹' ({1} : Set Nat)) := by
    exact IsClopen.preimage (⟨isClosed_singleton, isOpen_discrete _⟩ : IsClopen ({1} : Set Nat)) hg
  rcases isClopen_iff.mp hclopen with hempty | huniv
  · have hone : (1 : ℝ) ∈ g ⁻¹' ({1} : Set Nat) := by simp [hg1]
    rw [hempty] at hone
    exact hone.elim
  · have hzero : (0 : ℝ) ∈ g ⁻¹' ({1} : Set Nat) := by simp [huniv]
    simp [hg0] at hzero
