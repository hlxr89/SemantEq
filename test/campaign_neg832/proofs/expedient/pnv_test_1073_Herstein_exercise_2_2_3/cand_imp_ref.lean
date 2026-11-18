import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (G : Type*) [Group G] (h : ∀ (a b : G) (i : ℕ), (a * b)^i = a^i * b^i → (a * b)^(i+1) = a^(i+1) * b^(i+1)) : ∀ a b : G, a * b = b * a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_2_3 {G : Type*} [Group G]
  {P : ℕ → Prop} {hP : P = λ i => ∀ a b : G, (a*b)^i = a^i * b^i}
  (hP1 : ∃ n : ℕ, P n ∧ P (n+1) ∧ P (n+2)) : 
  ∀ a b : G, a*b = b*a := by
  subst P
  obtain ⟨n, hn, hn1, hn2⟩ := hP1
  intro a b
  have commPow (k : ℕ)
      (hk : (a * b) ^ k = a ^ k * b ^ k)
      (hk1 : (a * b) ^ (k + 1) = a ^ (k + 1) * b ^ (k + 1)) :
      b ^ k * a = a * b ^ k := by
    apply mul_left_cancel (a := a ^ k)
    apply mul_right_cancel (b := b)
    simpa [pow_succ, mul_assoc] using
      (calc
        a ^ k * (b ^ k * (a * b)) = (a ^ k * b ^ k) * (a * b) := by rw [mul_assoc]
        _ = (a * b) ^ k * (a * b) := congrArg (fun x => x * (a * b)) hk.symm
        _ = (a * b) ^ (k + 1) := (pow_succ _ _).symm
        _ = a ^ (k + 1) * b ^ (k + 1) := hk1)
  have hbn := commPow n (hn a b) (hn1 a b)
  have hbn1 := commPow (n + 1) (hn1 a b) (hn2 a b)
  have hba : b * a = a * b := by
    apply mul_left_cancel (a := b ^ n)
    calc
      b ^ n * (b * a) = b ^ (n + 1) * a := by rw [pow_succ, mul_assoc]
      _ = a * b ^ (n + 1) := hbn1
      _ = (a * b ^ n) * b := by rw [pow_succ, mul_assoc]
      _ = (b ^ n * a) * b := by rw [hbn]
      _ = b ^ n * (a * b) := by rw [mul_assoc]
  exact hba.symm
