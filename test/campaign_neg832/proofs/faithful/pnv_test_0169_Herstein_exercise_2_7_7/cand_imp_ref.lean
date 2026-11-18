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
    { toFun := fun p => (1, φ p.1)
      map_one' := by simp
      map_mul' := by intro x y; simp }
  let M : Subgroup (G × G') := N.prod ⊥
  letI : M.Normal := by
    dsimp [M]
    infer_instance
  have hM : (Subgroup.map ψ M).Normal := dummy_assumed ψ
  constructor
  intro y hy g
  obtain ⟨x, hx, rfl⟩ := (Subgroup.mem_map.mp hy)
  have hmem : (1, φ x) ∈ Subgroup.map ψ M := by
    apply Subgroup.mem_map.mpr
    refine ⟨(x, 1), ?_, ?_⟩
    · exact ⟨hx, by simp⟩
    · simp [ψ]
  have hconj := hM.conj_mem (1, φ x) hmem (1, g)
  obtain ⟨z, hz, heq⟩ := Subgroup.mem_map.mp hconj
  apply Subgroup.mem_map.mpr
  refine ⟨z.1, hz.1, ?_⟩
  have := congrArg Prod.snd heq
  simpa [ψ] using this
