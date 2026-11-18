import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

namespace Erdos316

-- ===== assumed statement (antecedent) =====
theorem erdos_316_assumed :
    ¬ ∀ A : Finset ℕ, 0 ∉ A → 1 ∉ A →
    ∑ n ∈ A, (1 / n : ℚ) < 2 → ∃ (A₁ A₂ : Finset ℕ),
      Disjoint A₁ A₂ ∧ A = A₁ ∪ A₂ ∧
      (1 ≤ ∑ n ∈ A₁, (1 / n : ℚ) ∨ 1 ≤ ∑ n ∈ A₂, (1 / n : ℚ)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
set_option maxHeartbeats 2000000 in
theorem erdos_316_goal :
    ¬ ∀ A : Finset ℕ, 0 ∉ A → 1 ∉ A →
    ∑ n ∈ A, (1 / n : ℚ) < 2 → ∃ (A₁ A₂ : Finset ℕ),
      Disjoint A₁ A₂ ∧ A = A₁ ∪ A₂ ∧
      ∑ n ∈ A₁, (1 / n : ℚ) < 1 ∧ ∑ n ∈ A₂, (1 / n : ℚ) <  1 := by
  let A : Finset ℕ := {2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16}
  intro h
  rcases h A (by native_decide) (by native_decide) (by norm_num [A]) with
    ⟨A₁, A₂, hd, hu, h₁, h₂⟩
  have hA₁ : A₁ ∈ A.powerset := Finset.mem_powerset.mpr (by
    intro n hn
    rw [hu]
    exact Finset.mem_union_left A₂ hn)
  have hA₂ : A₂ ∈ A.powerset := Finset.mem_powerset.mpr (by
    intro n hn
    rw [hu]
    exact Finset.mem_union_right A₁ hn)
  have hall : ∀ B : {B // B ∈ A.powerset},
      (∑ n ∈ B.1, (1 / n : ℚ)) < 1 → (∑ n ∈ B.1, (1 / n : ℚ)) ≤ 719 / 720 := by
    native_decide
  have hb₁ : (∑ n ∈ A₁, (1 / n : ℚ)) ≤ 719 / 720 :=
    hall ⟨A₁, hA₁⟩ h₁
  have hb₂ : (∑ n ∈ A₂, (1 / n : ℚ)) ≤ 719 / 720 :=
    hall ⟨A₂, hA₂⟩ h₂
  have hsum := Finset.sum_union hd (f := fun n : ℕ => (1 / n : ℚ))
  rw [← hu] at hsum
  norm_num [A] at hsum
  norm_num [div_eq_mul_inv] at hb₁ hb₂
  linarith

end Erdos316
