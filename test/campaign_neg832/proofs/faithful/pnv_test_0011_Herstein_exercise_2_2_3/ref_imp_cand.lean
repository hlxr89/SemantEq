import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_2_2_3_assumed {G : Type*} [Group G]
  {P : ℕ → Prop} {hP : P = λ i => ∀ a b : G, (a*b)^i = a^i * b^i}
  (hP1 : ∃ n : ℕ, P n ∧ P (n+1) ∧ P (n+2)) : 
  ∀ a b : G, a*b = b*a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {G : Type*} [Group G] (a b : G) (i : ℤ) (h : ∀ j ∈ ({i-1, i, i+1} : Finset ℤ), (a*b)^j = a^j * b^j) : Commute a b := by
  have step (j : ℤ)
      (hj : (a * b) ^ j = a ^ j * b ^ j)
      (hj1 : (a * b) ^ (j + 1) = a ^ (j + 1) * b ^ (j + 1)) :
      Commute a (b ^ j) := by
    have heq : a ^ j * (b ^ j * a) * b = a ^ j * (a * b ^ j) * b := by
      simpa only [zpow_add_one, hj, mul_assoc] using hj1
    have heq' : b ^ j * a = a * b ^ j := by
      exact mul_left_cancel (mul_right_cancel heq)
    exact heq'.symm
  have hi1 := h (i - 1) (by simp)
  have hi := h i (by simp)
  have hip1 := h (i + 1) (by simp)
  have hc1 : Commute a (b ^ (i - 1)) := step (i - 1) hi1 (by simpa using hi)
  have hc2 : Commute a (b ^ i) := step i hi hip1
  have hab : Commute a b := by
    have hc := hc2.mul_right hc1.inv_right
    simpa [← zpow_neg, ← zpow_add] using hc
  let H : Subgroup G := Subgroup.closure ({a, b} : Set G)
  letI : CommGroup H := Subgroup.closureCommGroupOfComm (k := ({a, b} : Set G)) (by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact hab.eq
    · exact hab.eq.symm
    · rfl)
  let aH : H := ⟨a, Subgroup.subset_closure (by simp)⟩
  let bH : H := ⟨b, Subgroup.subset_closure (by simp)⟩
  have hcomm : aH * bH = bH * aH := exercise_2_2_3_assumed
    (G := H) (P := fun k => ∀ x y : H, (x * y) ^ k = x ^ k * y ^ k)
    (hP := rfl) ⟨0, by simp, by simp, by
      intro x y
      exact (Commute.all x y).mul_pow 2⟩ aH bH
  exact congrArg Subtype.val hcomm
