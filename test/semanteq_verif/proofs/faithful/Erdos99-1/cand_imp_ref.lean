import Mathlib

open Set Metric EuclideanGeometry

-- ===== unified context (both sides' local defs, merged) =====
namespace Erdos99

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

def HasMinDist1 (A : Finset ℝ²) : Prop :=
  (∀ᵉ (p ∈ A) (q ∈ A), p ≠ q → dist p q ≥ 1) ∧
  (∃ᵉ (p ∈ A) (q ∈ A), dist p q = 1)

def FormsEquilateralTriangle (p q r : ℝ²) : Prop :=
  dist p q = 1 ∧ dist q r = 1 ∧ dist p r = 1

-- ===== assumed statement (antecedent) =====
theorem erdos_99_assumed :
    ∀ᶠ n in Filter.atTop, ∀ A : Finset ℝ²,
      (IsMinOn (fun B: Finset ℝ² => diam (B : Set ℝ²)) {B : Finset ℝ² | B.card = n ∧ HasMinDist1 B} A) →
      ∃ᵉ (p ∈ A) (q ∈ A) (r ∈ A), FormsEquilateralTriangle p q r := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_99_goal :
    ∀ᶠ n in Filter.atTop, ∀ A : Finset ℝ²,
      A.card = n → HasMinDist1 A →
      (IsMinOn (fun B: Finset ℝ² => diam (B : Set ℝ²)) {B : Finset ℝ² | B.card = n ∧ HasMinDist1 B} A) →
      ∃ᵉ (p ∈ A) (q ∈ A) (r ∈ A), FormsEquilateralTriangle p q r := by
  filter_upwards [erdos_99_assumed] with n hn
  intro A _ _ hmin
  exact hn A hmin

end Erdos99
