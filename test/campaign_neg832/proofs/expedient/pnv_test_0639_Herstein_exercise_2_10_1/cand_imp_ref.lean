import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (G : Type*) [Group G] (N : Subgroup G) [hN : N.Normal] (b : G) {p : ℕ} (hb : orderOf b = p) (hNb : ¬b ∈ N) : N ⊓ Subgroup.center G = ⊥ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_10_1 {G : Type*} [Group G] (A : Subgroup G)
  [A.Normal] {b : G} (hb : b ∉ A) (hp : Nat.Prime (orderOf b)) :
  A ⊓ (Subgroup.closure {b}) = ⊥ := by
  rw [← Subgroup.zpowers_eq_closure]
  apply le_antisymm
  · intro x hx
    let H := A.comap (Subgroup.zpowers b).subtype
    letI : Fact (Nat.card (Subgroup.zpowers b)).Prime := ⟨by
      simpa only [Nat.card_zpowers] using hp⟩
    rcases H.eq_bot_or_eq_top_of_prime_card with hH | hH
    · have hxH : (⟨x, hx.2⟩ : Subgroup.zpowers b) ∈ H := hx.1
      rw [hH] at hxH
      simpa only [Subgroup.mem_bot, Subtype.ext_iff] using hxH
    · exfalso
      apply hb
      have hbH : (⟨b, Subgroup.mem_zpowers b⟩ : Subgroup.zpowers b) ∈ H := by
        rw [hH]
        exact Subgroup.mem_top _
      exact hbH
  · exact bot_le
