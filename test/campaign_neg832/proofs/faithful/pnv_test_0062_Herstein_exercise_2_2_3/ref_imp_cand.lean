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
theorem dummy {G : Type*} [Group G] (a b : G) (h : ∀ i : ℕ, (a * b) ^ (i + 2) = a ^ i * b ^ i * a ^ i * b ^ i) : a * b = b * a := by
  have h0 := h 0
  have h1 := h 1
  simp only [zero_add, pow_two, pow_zero, one_mul, mul_one] at h0
  simp only [one_add_one_eq_two, pow_two, pow_one] at h1
  have hx2 : (a * b) ^ 2 = 1 := by simpa [pow_two] using h0
  have hx3 : (a * b) ^ 3 = 1 := by
    calc
      (a * b) ^ 3 = (a * b) * (a * b) := by simpa [mul_assoc] using h1
      _ = 1 := h0
  have hab : a * b = 1 := by
    calc
      a * b = (a * b) ^ 2 * (a * b) := by rw [hx2, one_mul]
      _ = (a * b) ^ 3 := (pow_succ (a * b) 2).symm
      _ = 1 := hx3
  have hb : b = a⁻¹ := eq_inv_of_mul_eq_one_right hab
  let H : Subgroup G := Subgroup.zpowers a
  let aa : H := ⟨a, Subgroup.mem_zpowers a⟩
  let bb : H := ⟨b, by rw [hb]; exact H.inv_mem (Subgroup.mem_zpowers a)⟩
  have hcomm : ∀ x y : H, x * y = y * x := by
    intro x y
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp x.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp y.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hm.symm, hn.symm]
    exact (Commute.refl a).zpow_zpow m n
  have htriple : ∃ n : ℕ, (∀ x y : H, (x * y) ^ n = x ^ n * y ^ n) ∧
      (∀ x y : H, (x * y) ^ (n + 1) = x ^ (n + 1) * y ^ (n + 1)) ∧
      (∀ x y : H, (x * y) ^ (n + 2) = x ^ (n + 2) * y ^ (n + 2)) := by
    refine ⟨0, ?_, ?_, ?_⟩
    · simp
    · simp
    · intro x y
      exact (show Commute x y from hcomm x y).mul_pow 2
  have hc := exercise_2_2_3_assumed
    (G := H)
    (P := fun i => ∀ x y : H, (x * y) ^ i = x ^ i * y ^ i)
    (hP := rfl) htriple aa bb
  exact congrArg Subtype.val hc
