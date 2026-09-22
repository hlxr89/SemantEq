import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_23_3_refs_assumed {X : Type*} [TopologicalSpace X]
  [TopologicalSpace X] {A : ℕ → Set X}
  (hAn : ∀ n, IsConnected (A n))
  (A₀ : Set X)
  (hA : IsConnected A₀)
  (h : ∀ n, A₀ ∩ A n ≠ ∅) :
  IsConnected (A₀ ∪ (⋃ n, A n)) :=
by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_23_3 {X : Type*} [TopologicalSpace X] {ι : Type*}
    (A : Set X) (Aa : ι → Set X)
    (hA : IsConnected A) (hAa : ∀ α, IsConnected (Aa α))
    (hmeet : ∀ α, (A ∩ Aa α).Nonempty) :
    IsConnected (A ∪ ⋃ α, Aa α) := by
  let s : Option ι → Set X
    | none => A
    | some α => A ∪ Aa α
  obtain ⟨x, hx⟩ := hA.nonempty
  have hs_inter : (⋂ i, s i).Nonempty := by
    refine ⟨x, ?_⟩
    simp only [Set.mem_iInter]
    intro i
    cases i with
    | none => exact hx
    | some α => exact Or.inl hx
  have hs_pre : ∀ i, IsPreconnected (s i) := by
    intro i
    cases i with
    | none => exact hA.isPreconnected
    | some α =>
        obtain ⟨y, hyA, hyAa⟩ := hmeet α
        exact IsPreconnected.union y hyA hyAa hA.isPreconnected (hAa α).isPreconnected
  have hs_eq : (⋃ i, s i) = A ∪ ⋃ α, Aa α := by
    ext z
    constructor
    · intro hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨i, hi⟩ := hz
      cases i with
      | none =>
          exact Or.inl hi
      | some α =>
          rcases hi with hi | hi
          · exact Or.inl hi
          · exact Or.inr (Set.mem_iUnion_of_mem α hi)
    · intro hz
      rcases hz with hz | hz
      · exact Set.mem_iUnion_of_mem none hz
      · simp only [Set.mem_iUnion] at hz
        obtain ⟨α, hα⟩ := hz
        exact Set.mem_iUnion_of_mem (some α) (Or.inr hα)
  constructor
  · exact ⟨x, by simp [hx]⟩
  · rw [← hs_eq]
    exact isPreconnected_iUnion hs_inter hs_pre
