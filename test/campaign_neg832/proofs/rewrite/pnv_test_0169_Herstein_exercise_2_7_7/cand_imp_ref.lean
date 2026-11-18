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
  let F : G × G' →* G × G' :=
    (MonoidHom.inr G G').comp (φ.comp (MonoidHom.fst G G'))
  have h : (Subgroup.map F (N.prod ⊤)).Normal :=
    dummy_assumed F (N := N.prod ⊤)
  have hc := h.comap (MonoidHom.inr G G')
  rw [show Subgroup.comap (MonoidHom.inr G G') (Subgroup.map F (N.prod ⊤)) =
      Subgroup.map φ N by
    ext y
    simp only [Subgroup.mem_comap, Subgroup.mem_map, Subgroup.mem_prod, Subgroup.mem_top,
      and_true]
    constructor
    · rintro ⟨x, hx, hxy⟩
      refine ⟨x.1, hx, ?_⟩
      change (1, φ x.1) = (1, y) at hxy
      exact congrArg Prod.snd hxy
    · rintro ⟨x, hx, hxy⟩
      refine ⟨(x, 1), hx, ?_⟩
      change (1, φ x) = (1, y)
      rw [hxy]] at *
  exact hc
