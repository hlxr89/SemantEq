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
theorem problem_statement_assumed
  (A B C A₁ B₁ P Q P₁ Q₁ : ℝ × ℝ)
  (h_triangle : A ≠ B ∧ B ≠ C ∧ C ≠ A)
  (h_A1_on_BC : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ A₁ = (1 - t) • B + t • C)
  (h_B1_on_AC : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ B₁ = (1 - t) • A + t • C)
  (h_P_on_AA1 : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ P = (1 - t) • A + t • A₁)
  (h_Q_on_BB1 : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ Q = (1 - t) • B + t • B₁)
  (h_PQ_parallel_AB : ∃ k : ℝ, k ≠ 0 ∧ Q - P = k • (B - A))
  (h_B1_between_P_P1 : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ P₁ = (1 - t) • P + t • B₁)
  (h_P1_on_line_PB1 : ∃ s : ℝ, P₁ = (1 - s) • P + s • B₁)
  (h_angle_PP1C : ∃ (angle : ℝ), angle = Real.arccos (((P₁ - P).1 * (C - P₁).1 + (P₁ - P).2 * (C - P₁).2) / (dist P₁ P * dist C P₁)) ∧
                    angle = Real.arccos (((B - A).1 * (C - A).1 + (B - A).2 * (C - A).2) / (dist B A * dist C A)))
  (h_A1_between_Q_Q1 : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ Q₁ = (1 - t) • Q + t • A₁)
  (h_Q1_on_line_QA1 : ∃ s : ℝ, Q₁ = (1 - s) • Q + s • A₁)
  (h_angle_CQ1Q : ∃ (angle : ℝ), angle = Real.arccos (((Q₁ - C).1 * (Q - Q₁).1 + (Q₁ - C).2 * (Q - Q₁).2) / (dist Q₁ C * dist Q Q₁)) ∧
                    angle = Real.arccos (((B - A).1 * (B - A).1 + (B - A).2 * (B - A).2) / (dist B A * dist B A)))
  : ∃ (center : ℝ × ℝ) (radius : ℝ), radius > 0 ∧
    dist P center = radius ∧
    dist Q center = radius ∧
    dist P₁ center = radius ∧
    dist Q₁ center = radius := by
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
  exfalso
  have h := problem_statement_assumed
    ((0, 0) : ℝ × ℝ) ((1, 1) : ℝ × ℝ) ((2, 2) : ℝ × ℝ)
    ((3 / 2, 3 / 2) : ℝ × ℝ) ((1, 1) : ℝ × ℝ)
    ((1 / 2, 1 / 2) : ℝ × ℝ) ((1, 1) : ℝ × ℝ)
    ((3 / 4, 3 / 4) : ℝ × ℝ) ((5 / 4, 5 / 4) : ℝ × ℝ)
    (by norm_num)
    (by refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩; norm_num [Prod.ext_iff])
    (by refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩; norm_num [Prod.ext_iff])
    (by refine ⟨1 / 3, by norm_num, by norm_num, ?_⟩; norm_num [Prod.ext_iff])
    (by refine ⟨0, by norm_num, by norm_num, ?_⟩; norm_num [Prod.ext_iff])
    (by refine ⟨1 / 2, by norm_num, ?_⟩; norm_num [Prod.ext_iff])
    (by refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩; norm_num [Prod.ext_iff])
    (by refine ⟨1 / 2, ?_⟩; norm_num [Prod.ext_iff])
    (by refine ⟨Real.arccos 2, ?_, ?_⟩ <;> norm_num [Prod.dist_eq, Real.dist_eq])
    (by refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩; norm_num [Prod.ext_iff])
    (by refine ⟨1 / 2, ?_⟩; norm_num [Prod.ext_iff])
    (by refine ⟨Real.arccos 2, ?_, ?_⟩ <;> norm_num [Prod.dist_eq, Real.dist_eq])
  obtain ⟨center, radius, hradius, hP, hQ, hP₁, hQ₁⟩ := h
  rcases center with ⟨x, y⟩
  simp only [Prod.dist_eq, Real.dist_eq] at hP hQ hP₁ hQ₁
  norm_num at hP hQ hP₁ hQ₁
  have hPx : |1 / 2 - x| ≤ radius := (le_max_left _ _).trans_eq hP
  have hPy : |1 / 2 - y| ≤ radius := (le_max_right _ _).trans_eq hP
  have hQx : |1 - x| ≤ radius := (le_max_left _ _).trans_eq hQ
  have hQy : |1 - y| ≤ radius := (le_max_right _ _).trans_eq hQ
  rw [abs_le] at hPx hPy hQx hQy
  have hx : |3 / 4 - x| < radius := by
    rw [abs_lt]
    constructor <;> linarith
  have hy : |3 / 4 - y| < radius := by
    rw [abs_lt]
    constructor <;> linarith
  have hm : max |3 / 4 - x| |3 / 4 - y| < radius := max_lt hx hy
  linarith
