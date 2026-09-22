import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} (hp : Nat.Prime p) : (∃ (res nonres : Finset (ZMod p)), res.card = (p - 1) / 2 ∧ nonres.card = (p - 1) / 2 ∧ (∀ a ∈ res, ∃ b : ZMod p, b^2 = a) ∧ (∀ a ∈ nonres, ∀ b : ZMod p, b^2 ≠ a) ∧ ∀ x : ZMod p, x ≠ 0 → (x ∈ res ∨ x ∈ nonres)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4_9 (p : ℕ) (hp : Nat.Prime p) (hodd : p % 2 = 1) :
  (∃ S : Finset (ZMod p), 0 ∉ S ∧ S.card = (p-1)/2 ∧ ∀ q ∈ S, ∃ x : ZMod p, x^2 = q) ∧
  (∃ S : Finset (ZMod p), 0 ∉ S ∧ S.card = (p-1)/2 ∧ ∀ q ∈ S, ¬ ∃ x : ZMod p, x^2 = q) := by
  rcases dummy_assumed hp with
    ⟨res, nonres, hres_card, hnonres_card, hres, hnonres, hcover⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hdisjoint : Disjoint res nonres := Finset.disjoint_left.mpr (by
    intro a ha_res ha_nonres
    rcases hres a ha_res with ⟨b, hb⟩
    exact hnonres a ha_nonres b hb)
  have hunion_card : (res ∪ nonres).card = p - 1 := by
    rw [Finset.card_union_of_disjoint hdisjoint, hres_card, hnonres_card]
    omega
  have hnonzero_card : (Finset.univ.erase (0 : ZMod p)).card = p - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, ZMod.card]
  have hnonzero_subset : Finset.univ.erase (0 : ZMod p) ⊆ res ∪ nonres := by
    intro x hx
    have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
    exact Finset.mem_union.mpr (hcover x hx0)
  have hunion_eq : Finset.univ.erase (0 : ZMod p) = res ∪ nonres :=
    Finset.eq_of_subset_of_card_le hnonzero_subset (by
      rw [hunion_card, hnonzero_card])
  have hzero_res : 0 ∉ res := by
    intro hz
    have : (0 : ZMod p) ∈ res ∪ nonres := Finset.mem_union_left nonres hz
    rw [← hunion_eq] at this
    simpa using this
  have hzero_nonres : 0 ∉ nonres := by
    intro hz
    exact hnonres 0 hz 0 (by simp)
  refine ⟨⟨res, hzero_res, hres_card, hres⟩, ⟨nonres, hzero_nonres, hnonres_card, ?_⟩⟩
  intro q hq hsq
  rcases hsq with ⟨x, hx⟩
  exact hnonres q hq x hx
