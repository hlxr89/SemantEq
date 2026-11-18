import Mathlib

open Affine Affine.Simplex EuclideanGeometry FiniteDimensional Module

open scoped Affine EuclideanGeometry Real

-- ===== unified context (both sides' local defs, merged) =====
-- Empty: neither preamble contains local definitions or structures.

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable (V : Type*) (Pt : Type*)

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]

variable [NormedAddTorsor V Pt]

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (A B C A₁ B₁ P Q P₁ Q₁ : E)
  (hA₁_on_BC : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ A₁ = (1 - t) • B + t • C)
  (hB₁_on_AC : ∃ s : ℝ, 0 < s ∧ s < 1 ∧ B₁ = (1 - s) • A + s • C)
  (hP_on_AA₁ : ∃ u : ℝ, 0 < u ∧ u < 1 ∧ P = (1 - u) • A + u • A₁)
  (hQ_on_BB₁ : ∃ v : ℝ, 0 < v ∧ v < 1 ∧ Q = (1 - v) • B + v • B₁)
  (hPQ_parallel_AB : ∃ k : ℝ, k ≠ 0 ∧ P - Q = k • (A - B))
  (hP₁_on_line_PB₁ : ∃ t : ℝ, P₁ = (1 - t) • P + t • B₁)
  (hB₁_between_P_P₁ : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ P₁ = (1 - t) • P + t • B₁)
  (hQ₁_on_line_QA₁ : ∃ s : ℝ, Q₁ = (1 - s) • Q + s • A₁)
  (hA₁_between_Q_Q₁ : ∃ s : ℝ, 0 < s ∧ s < 1 ∧ Q₁ = (1 - s) • Q + s • A₁)
  (h_angle_P : ∃ (angle : E → E → E → ℝ), angle P P₁ C = angle B A C)
  (h_angle_Q : ∃ (angle : E → E → E → ℝ), angle C Q₁ Q = angle C B A) :
  ∃ (center : E) (radius : ℝ), radius > 0 ∧ 
    ‖P - center‖ = radius ∧ 
    ‖Q - center‖ = radius ∧ 
    ‖P₁ - center‖ = radius ∧ 
    ‖Q₁ - center‖ = radius := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2019_p2 [Fact (finrank ℝ V = 2)] (A B C A₁ B₁ P Q P₁ Q₁ : Pt)
    (affine_independent_ABC : AffineIndependent ℝ ![A, B, C]) (wbtw_B_A₁_C : Wbtw ℝ B A₁ C)
    (wbtw_A_B₁_C : Wbtw ℝ A B₁ C) (wbtw_A_P_A₁ : Wbtw ℝ A P A₁) (wbtw_B_Q_B₁ : Wbtw ℝ B Q B₁)
    (PQ_parallel_AB : line[ℝ, P, Q] ∥ line[ℝ, A, B]) (P_ne_Q : P ≠ Q)
    (sbtw_P_B₁_P₁ : Sbtw ℝ P B₁ P₁) (angle_PP₁C_eq_angle_BAC : ∠ P P₁ C = ∠ B A C)
    (C_ne_P₁ : C ≠ P₁) (sbtw_Q_A₁_Q₁ : Sbtw ℝ Q A₁ Q₁)
    (angle_CQ₁Q_eq_angle_CBA : ∠ C Q₁ Q = ∠ C B A) (C_ne_Q₁ : C ≠ Q₁) :
    Concyclic ({P, Q, P₁, Q₁} : Set Pt) := by
  -- not proved: the candidate theorem concerns vector-space points and uses reversed betweenness equations, so its conclusion cannot be transported to this affine-torsor statement
  sorry
