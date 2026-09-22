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
  rcases dummy_assumed hp with
    ⟨res, nonres, hrescard, hnonrescard, hres, hnonres, hcover⟩
  have hd : Disjoint res nonres := Finset.disjoint_left.2 (by
    intro a hr hn
    rcases hres a hr with ⟨b, hb⟩
    exact hnonres a hn b hb)
  have hce : (Finset.univ.erase (0 : ZMod p)).card = p - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod p)), Finset.card_univ,
      ZMod.card]
  have hcu : (res ∪ nonres).card = p - 1 := by
    rw [Finset.card_union_of_disjoint hd, hrescard, hnonrescard]
    omega
  have hsub : Finset.univ.erase (0 : ZMod p) ⊆ res ∪ nonres := by
    intro x hx
    rw [Finset.mem_erase] at hx
    exact Finset.mem_union.2 (hcover x hx.1)
  have heq : Finset.univ.erase (0 : ZMod p) = res ∪ nonres :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hres0 : (0 : ZMod p) ∉ res := by
    intro hz
    have : (0 : ZMod p) ∈ Finset.univ.erase (0 : ZMod p) := by
      rw [heq]
      exact Finset.mem_union.2 (Or.inl hz)
    exact (Finset.mem_erase.1 this).1 rfl
  have hnonres0 : (0 : ZMod p) ∉ nonres := by
    intro hz
    exact hnonres 0 hz 0 (by simp)
  refine ⟨⟨res, hres0, hrescard, hres⟩, ⟨nonres, hnonres0, hnonrescard, ?_⟩⟩
  intro q hq hex
  rcases hex with ⟨x, hx⟩
  exact hnonres q hq x hx
