import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] (φ : G →* G) {N : Subgroup G} [hN : N.Normal] : (Subgroup.map φ N).Normal := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_7_7 {G : Type*} [Group G] {G' : Type*} [Group G']
  (φ : G →* G') (N : Subgroup G) [N.Normal] :
  (Subgroup.map φ N).Normal  := by
  let ψ : G × G' →* G × G' :=
    { toFun := fun x ↦ (1, φ x.1)
      map_one' := by simp
      map_mul' := by intro x y; simp }
  have hnormal : (Subgroup.map ψ (N.prod ⊤)).Normal := dummy_assumed ψ
  constructor
  intro n hn g
  rw [Subgroup.mem_map] at hn ⊢
  rcases hn with ⟨x, hx, rfl⟩
  have hp : (1, φ x) ∈ Subgroup.map ψ (N.prod ⊤) := by
    rw [Subgroup.mem_map]
    exact ⟨(x, 1), ⟨hx, trivial⟩, by simp [ψ]⟩
  have hc := hnormal.conj_mem (1, φ x) hp (1, g)
  rw [Subgroup.mem_map] at hc
  rcases hc with ⟨y, hy, heq⟩
  refine ⟨y.1, hy.1, ?_⟩
  have heq' := congrArg Prod.snd heq
  simpa [ψ] using heq'
