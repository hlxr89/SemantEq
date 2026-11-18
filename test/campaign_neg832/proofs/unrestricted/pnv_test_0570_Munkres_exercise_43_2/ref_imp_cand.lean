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
  have h := exercise_43_2_assumed (X := Unit) (Y := Nat)
    (∅ : Set Unit) (fun _ => 0) uniformContinuous_const.uniformContinuousOn
  rcases h with ⟨g, hg, huniq⟩
  have hfalse : ContinuousOn (fun _ : Unit => (0 : Nat)) (closure (∅ : Set Unit)) ∧
      UniformContinuousOn (fun _ : Unit => (0 : Nat)) (closure (∅ : Set Unit)) ∧
      ∀ (x : (∅ : Set Unit)), (fun _ : Unit => (0 : Nat)) x = (fun _ => 0) x := by
    refine ⟨by simp, uniformContinuous_const.uniformContinuousOn, ?_⟩
    intro x
    exact x.property.elim
  have htrue : ContinuousOn (fun _ : Unit => (1 : Nat)) (closure (∅ : Set Unit)) ∧
      UniformContinuousOn (fun _ : Unit => (1 : Nat)) (closure (∅ : Set Unit)) ∧
      ∀ (x : (∅ : Set Unit)), (fun _ : Unit => (1 : Nat)) x = (fun _ => 0) x := by
    refine ⟨by simp, uniformContinuous_const.uniformContinuousOn, ?_⟩
    intro x
    exact x.property.elim
  have heq : (fun _ : Unit => (0 : Nat)) = (fun _ : Unit => (1 : Nat)) :=
    (huniq _ hfalse).trans (huniq _ htrue).symm
  have hbad : (0 : Nat) = 1 := congrFun heq ()
  simp at hbad

