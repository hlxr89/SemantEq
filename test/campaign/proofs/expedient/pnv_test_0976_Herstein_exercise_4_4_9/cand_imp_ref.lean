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
  rcases dummy_assumed hp with ⟨res, nonres, hres, hncard, hrsq, hnrsq, hcover⟩
  have hdisj : Disjoint res nonres := by
    rw [Finset.disjoint_left]
    intro a har han
    rcases hrsq a har with ⟨b, hb⟩
    exact hnrsq a han b hb
  have hsub : Finset.univ.erase 0 ⊆ res ∪ nonres := by
    intro a ha
    rw [Finset.mem_erase] at ha
    exact Finset.mem_union.mpr (hcover a ha.1)
  have hucard : (res ∪ nonres).card = p - 1 := by
    rw [Finset.card_union_of_disjoint hdisj, hres, hncard]
    omega
  have hecard : (Finset.univ.erase (0 : ZMod p)).card = p - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, ZMod.card]
  have heq : Finset.univ.erase (0 : ZMod p) = res ∪ nonres := by
    apply Finset.eq_of_subset_of_card_le hsub
    omega
  refine ⟨⟨res, ?_, hres, hrsq⟩, ⟨nonres, ?_, hncard, ?_⟩⟩
  · intro hzero
    have : (0 : ZMod p) ∈ res ∪ nonres := Finset.mem_union_left nonres hzero
    rw [← heq] at this
    simp at this
  · intro hzero
    have : (0 : ZMod p) ∈ res ∪ nonres := Finset.mem_union_right res hzero
    rw [← heq] at this
    simp at this
  · intro q hq ⟨x, hx⟩
    exact hnrsq q hq x hx
