import Mathlib

open Affine Affine.Simplex EuclideanGeometry FiniteDimensional Module

open scoped Affine EuclideanGeometry Real

-- ===== unified context (both sides' local defs, merged) =====
-- There are no local definitions or structures in either preamble.
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
set_option maxHeartbeats 800000 in
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
    (0, 0) (1, 1) (4, 4) (4, 4) (3, 3) (0, 0) (1, 1) (2, 2) (3, 3)
    (by norm_num)
    (by refine ⟨1, ?_⟩; norm_num)
    (by refine ⟨3 / 4, ?_⟩; norm_num)
    (by refine ⟨0, ?_⟩; norm_num)
    (by refine ⟨0, ?_⟩; norm_num)
    (by refine ⟨1, ?_⟩; norm_num)
    (by refine ⟨2 / 3, ?_⟩; norm_num)
    (by refine ⟨2 / 3, ?_⟩; norm_num)
    (by refine ⟨0, ?_⟩; norm_num [Prod.dist_eq, Real.dist_eq, Real.arccos_of_one_le])
    (by refine ⟨2 / 3, ?_⟩; norm_num)
    (by refine ⟨2 / 3, ?_⟩; norm_num)
    (by refine ⟨0, ?_⟩; norm_num [Prod.dist_eq, Real.dist_eq, Real.arccos_of_one_le])
  obtain ⟨c, r, hr, h0, h1, h2, h3⟩ := h
  have h0' := congrArg (fun x : ℝ => x ^ 2) h0
  have h1' := congrArg (fun x : ℝ => x ^ 2) h1
  have h2' := congrArg (fun x : ℝ => x ^ 2) h2
  have h3' := congrArg (fun x : ℝ => x ^ 2) h3
  rcases c with ⟨x, y⟩
  norm_num [Prod.dist_eq, Real.dist_eq, max_def] at h0' h1' h2' h3'
  have abs_sq_le_abs_sq {a b : ℝ} (hab : |a| ≤ |b|) : a ^ 2 ≤ b ^ 2 := by
    nlinarith [sq_nonneg (|b| - |a|), sq_abs a, sq_abs b, abs_nonneg a, abs_nonneg b]
  split_ifs at h0' with h00 <;>
  split_ifs at h1' with h11 <;>
  split_ifs at h2' with h22 <;>
  split_ifs at h3' with h33 <;>
    norm_num [sq_abs] at h0' h1' h2' h3'
  all_goals
    first | have q0 := abs_sq_le_abs_sq h00 | have q0 := abs_sq_le_abs_sq (le_of_not_ge h00)
    first | have q1 := abs_sq_le_abs_sq h11 | have q1 := abs_sq_le_abs_sq (le_of_not_ge h11)
    first | have q2 := abs_sq_le_abs_sq h22 | have q2 := abs_sq_le_abs_sq (le_of_not_ge h22)
    first | have q3 := abs_sq_le_abs_sq h33 | have q3 := abs_sq_le_abs_sq (le_of_not_ge h33)
    nlinarith
