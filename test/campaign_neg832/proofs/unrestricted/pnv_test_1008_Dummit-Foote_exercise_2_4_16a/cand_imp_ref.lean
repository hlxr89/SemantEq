import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed [Group G] [Finite G] (H : Subgroup G) [Subgroup.Normal H] (hH : H ≠ ⊤) : ∃ M : Subgroup G, H ≤ M ∧ ∀ N : Subgroup G, H ≤ N → N = M ∨ N = ⊤ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_4_16a {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
  (hH : H ≠ ⊤) :
  ∃ M : Subgroup G, M ≠ ⊤ ∧
  (∀ K : Subgroup G, M ≤ K → K = M ∨ K = ⊤) ∧
  H ≤ M := by
  classical
  let f : Multiplicative (ZMod 4) →* Multiplicative (ZMod 2) :=
    (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)).toAddMonoidHom.toMultiplicative
  let N : Subgroup (Multiplicative (ZMod 4)) := f.ker
  have hbot : (⊥ : Subgroup (Multiplicative (ZMod 4))) ≠ ⊤ := by
    intro h
    have hx : Multiplicative.ofAdd (1 : ZMod 4) ∈ (⊥ : Subgroup (Multiplicative (ZMod 4))) := by
      rw [h]
      trivial
    exact (by native_decide : (1 : ZMod 4) ≠ 0) (by simpa using hx)
  obtain ⟨M, hle, hmax⟩ :=
    dummy_assumed (G := Multiplicative (ZMod 4))
      (⊥ : Subgroup (Multiplicative (ZMod 4))) hbot
  have hM : M = ⊥ := by
    rcases hmax (⊥ : Subgroup (Multiplicative (ZMod 4))) le_rfl with h | h
    · exact h.symm
    · exact (hbot h).elim
  have hN_ne_bot : N ≠ ⊥ := by
    intro h
    have hx : Multiplicative.ofAdd (2 : ZMod 4) ∈ N := by
      change f (Multiplicative.ofAdd (2 : ZMod 4)) = 1
      native_decide
    rw [h] at hx
    exact (by native_decide : (2 : ZMod 4) ≠ 0) (by simpa using hx)
  have hN_ne_top : N ≠ ⊤ := by
    intro h
    have hx : Multiplicative.ofAdd (1 : ZMod 4) ∈ N := by
      rw [h]
      trivial
    change f (Multiplicative.ofAdd (1 : ZMod 4)) = 1 at hx
    exact (by native_decide : f (Multiplicative.ofAdd (1 : ZMod 4)) ≠ 1) hx
  rcases hmax N bot_le with h | h
  · exact (hN_ne_bot (h.trans hM)).elim
  · exact (hN_ne_top h).elim
