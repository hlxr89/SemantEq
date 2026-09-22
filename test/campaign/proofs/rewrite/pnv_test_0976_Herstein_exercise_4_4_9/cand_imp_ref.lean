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
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨res, nonres, hres_card, hnonres_card, hres, hnonres, hcover⟩ := dummy_assumed hp
  have hdisjoint : Disjoint res nonres := Finset.disjoint_left.mpr (by
    intro a ha hna
    obtain ⟨b, hb⟩ := hres a ha
    exact (hnonres a hna b) hb)
  have hhalf : (p - 1) / 2 + (p - 1) / 2 = p - 1 := by
    have hdiv : 2 ∣ p - 1 := ⟨p / 2, (Nat.two_mul_odd_div_two hodd).symm⟩
    rw [← two_mul, Nat.mul_div_cancel' hdiv]
  have hunion_card : (res ∪ nonres).card = p - 1 := by
    rw [Finset.card_union_of_disjoint hdisjoint, hres_card, hnonres_card, hhalf]
  have herase_card : (Finset.univ.erase (0 : ZMod p)).card = p - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, ZMod.card]
  have herase_subset : Finset.univ.erase (0 : ZMod p) ⊆ res ∪ nonres := by
    intro x hx
    exact Finset.mem_union.mpr (hcover x (Finset.ne_of_mem_erase hx))
  have herase_eq : Finset.univ.erase (0 : ZMod p) = res ∪ nonres :=
    Finset.eq_of_subset_of_card_le herase_subset (by rw [hunion_card, herase_card])
  have hzero_res : (0 : ZMod p) ∉ res := by
    intro hzero
    have : (0 : ZMod p) ∈ Finset.univ.erase 0 := by
      rw [herase_eq]
      exact Finset.mem_union.mpr (Or.inl hzero)
    exact (Finset.ne_of_mem_erase this) rfl
  constructor
  · exact ⟨res, hzero_res, hres_card, hres⟩
  · refine ⟨nonres, ?_, hnonres_card, ?_⟩
    · intro hzero
      exact (hnonres 0 hzero 0) (by simp only [pow_two, zero_mul])
    · intro q hq hq_square
      obtain ⟨x, hx⟩ := hq_square
      exact (hnonres q hq x) hx
