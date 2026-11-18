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
theorem dummy {G : Type*} [Group G] (a b : G) (i : ℤ) (h : ∀ j : ℤ, j = i + 1 ∨ j = i + 2 → a * b ^ j = a ^ j * b ^ j) : Commute a b := by
  have href := exercise_2_2_3_assumed (G := PUnit.{1})
    (P := λ i => ∀ a b : PUnit.{1}, (a * b) ^ i = a ^ i * b ^ i)
    (hP := rfl)
    ⟨0,
      (λ _ _ => Subsingleton.elim _ _),
      (λ _ _ => Subsingleton.elim _ _),
      (λ _ _ => Subsingleton.elim _ _)⟩
  have _ := href (PUnit.unit : PUnit.{1}) PUnit.unit
  have h₁ := h (i + 1) (Or.inl rfl)
  have h₂ := h ((i + 1) + 1) (Or.inr (by
    simp only [add_assoc, one_add_one_eq_two]))
  have ha₁ : a = a ^ (i + 1) := mul_right_cancel h₁
  have ha₂ : a = a ^ ((i + 1) + 1) := mul_right_cancel h₂
  have haa : a = a * a := by
    rw [zpow_add_one, ← ha₁] at ha₂
    exact ha₂
  have ha : a = 1 := by
    apply Eq.symm
    apply mul_left_cancel (a := a)
    simpa only [mul_one] using haa
  rw [ha]
  exact Commute.one_left b
