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
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι => simpa using hA
  | inr hι =>
      letI := hι
      have hc : ∀ α, IsConnected (A ∪ Aa α) := fun α => hA.union (hmeet α) (hAa α)
      have hU : IsConnected (⋃ α, A ∪ Aa α) := by
        refine ⟨?_, isPreconnected_iUnion ?_ (fun α => (hc α).isPreconnected)⟩
        · exact nonempty_iUnion.2 ⟨Classical.choice hι, (hc _).nonempty⟩
        · obtain ⟨x, hx⟩ := hA.nonempty
          exact ⟨x, mem_iInter.2 fun _ => Or.inl hx⟩
      simpa [iUnion_union_distrib, iUnion_const] using hU
