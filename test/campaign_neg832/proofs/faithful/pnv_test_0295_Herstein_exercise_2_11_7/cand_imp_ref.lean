import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (G : Type*) [Group G] {P : Subgroup G} (hP : IsPGroup p P) (hPn : P.Normal) (hPs : IsPGroup p (G ⧸ P)) : ∀ (φ : G →* G), φ.range = P := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_11_7 {G : Type*} [Group G] {p : ℕ} (hp : Nat.Prime p)
  {P : Sylow p G} (hP : P.Normal) :
  Subgroup.Characteristic (P : Subgroup G) := by
  have hquot : IsPGroup p (P ⧸ (⊥ : Subgroup P)) :=
    P.2.of_equiv QuotientGroup.quotientBot.symm
  have htriv : (⊤ : Subgroup P) = ⊥ := by
    rw [← (MonoidHom.range_eq_top (f := MonoidHom.id P)).mpr Function.surjective_id]
    exact dummy_assumed P (P := (⊥ : Subgroup P)) IsPGroup.of_bot
      Subgroup.normal_bot hquot (MonoidHom.id P)
  have hPbot : (P : Subgroup G) = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hx' : (⟨x, hx⟩ : P) ∈ (⊤ : Subgroup P) := Subgroup.mem_top _
      rw [htriv] at hx'
      exact congrArg Subtype.val hx'
    · exact bot_le
  rw [hPbot]
  exact Subgroup.botCharacteristic
