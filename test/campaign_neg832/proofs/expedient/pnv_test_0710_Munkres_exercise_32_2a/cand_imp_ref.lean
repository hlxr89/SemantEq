import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, CompactSpace (X i)] (h : ∀ i, Nonempty (X i)) (hX : ∀ i, T2Space (X i)) (h'X : T2Space (∀ i, X i)) : ∀ i, T2Space (X i) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_32_2a
  {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, Nonempty (X i)) (h2 : T2Space (Π i, X i)) :
  ∀ i, T2Space (X i) := by
  classical
  intro i
  letI := h2
  let f : X i → (∀ j, X j) := fun x j => if hij : j = i then hij ▸ x else Classical.choice (h j)
  apply T2Space.of_injective_continuous (f := f)
  · intro x y hxy
    have := congrFun hxy i
    simpa [f] using this
  · apply continuous_pi
    intro j
    by_cases hij : j = i
    · subst j
      simpa [f] using (continuous_id : Continuous (id : X i → X i))
    · simpa [f, hij] using (continuous_const : Continuous (fun _ : X i => Classical.choice (h j)))
