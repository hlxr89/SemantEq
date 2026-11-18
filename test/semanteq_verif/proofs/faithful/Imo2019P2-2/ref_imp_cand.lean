import Mathlib

open Affine Affine.Simplex EuclideanGeometry FiniteDimensional Module
open Real

open scoped Affine EuclideanGeometry Real

-- ===== unified context (both sides' local defs, merged) =====
-- There are no local definitions or structures.
attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable (V : Type*) (Pt : Type*)

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]

variable [NormedAddTorsor V Pt]

-- ===== assumed statement (antecedent) =====
theorem imo2019_p2_assumed [Fact (finrank ℝ V = 2)] (A B C A₁ B₁ P Q P₁ Q₁ : Pt)
    (affine_independent_ABC : AffineIndependent ℝ ![A, B, C]) (wbtw_B_A₁_C : Wbtw ℝ B A₁ C)
    (wbtw_A_B₁_C : Wbtw ℝ A B₁ C) (wbtw_A_P_A₁ : Wbtw ℝ A P A₁) (wbtw_B_Q_B₁ : Wbtw ℝ B Q B₁)
    (PQ_parallel_AB : line[ℝ, P, Q] ∥ line[ℝ, A, B]) (P_ne_Q : P ≠ Q)
    (sbtw_P_B₁_P₁ : Sbtw ℝ P B₁ P₁) (angle_PP₁C_eq_angle_BAC : ∠ P P₁ C = ∠ B A C)
    (C_ne_P₁ : C ≠ P₁) (sbtw_Q_A₁_Q₁ : Sbtw ℝ Q A₁ Q₁)
    (angle_CQ₁Q_eq_angle_CBA : ∠ C Q₁ Q = ∠ C B A) (C_ne_Q₁ : C ≠ Q₁) :
    Concyclic ({P, Q, P₁, Q₁} : Set Pt) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement :
  ∀ (A B C A₁ B₁ P Q P₁ Q₁ : ℝ × ℝ),
  -- A₁ is on segment BC
  (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ A₁ = (1 - t) • B + t • C) →
  -- B₁ is on segment AC
  (∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ B₁ = (1 - s) • A + s • C) →
  -- P is on segment AA₁
  (∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ P = (1 - u) • A + u • A₁) →
  -- Q is on segment BB₁
  (∃ v : ℝ, 0 ≤ v ∧ v ≤ 1 ∧ Q = (1 - v) • B + v • B₁) →
  -- PQ is parallel to AB
  (∃ k : ℝ, Q - P = k • (B - A)) →
  -- P₁ is on line PB₁, B₁ strictly between P and P₁
  (∃ w : ℝ, w > 1 ∧ P₁ = (1 - w) • P + w • B₁) →
  -- ∠PP₁C = ∠BAC
  (∃ (angle_P P₁_C : ℝ), 
    -- angle condition for PP₁C = BAC
    True) →
  -- Q₁ is on line QA₁, A₁ strictly between Q and Q₁
  (∃ z : ℝ, z > 1 ∧ Q₁ = (1 - z) • Q + z • A₁) →
  -- ∠CQ₁Q = ∠CBA
  (∃ (angle_Q Q₁_C : ℝ),
    -- angle condition for CQ₁Q = CBA
    True) →
  -- P, Q, P₁, Q₁ are concyclic
  ∃ (center : ℝ × ℝ) (radius : ℝ), radius > 0 ∧
    (center.1 - P.1)^2 + (center.2 - P.2)^2 = radius^2 ∧
    (center.1 - Q.1)^2 + (center.2 - Q.2)^2 = radius^2 ∧
    (center.1 - P₁.1)^2 + (center.2 - P₁.2)^2 = radius^2 ∧
    (center.1 - Q₁.1)^2 + (center.2 - Q₁.2)^2 = radius^2 := by
  -- not proved: the candidate drops essential angle and nondegeneracy hypotheses and is false.
  sorry
