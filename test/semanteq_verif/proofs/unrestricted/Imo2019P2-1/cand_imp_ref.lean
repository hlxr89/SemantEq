import Mathlib

open Affine Affine.Simplex EuclideanGeometry FiniteDimensional Module
open Real

open scoped Affine EuclideanGeometry Real

-- ===== unified context (both sides' local defs, merged) =====
-- empty

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable (V : Type*) (Pt : Type*)

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]

variable [NormedAddTorsor V Pt]

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  ∀ (A B C A₁ B₁ P Q P₁ Q₁ : ℝ × ℝ),
  -- A₁ lies on side BC (strictly between B and C)
  (∃ t : ℝ, 0 < t ∧ t < 1 ∧ A₁ = (1 - t) • B + t • C) →
  -- B₁ lies on side AC (strictly between A and C)
  (∃ s : ℝ, 0 < s ∧ s < 1 ∧ B₁ = (1 - s) • A + s • C) →
  -- P lies on segment AA₁ (strictly between A and A₁)
  (∃ u : ℝ, 0 < u ∧ u < 1 ∧ P = (1 - u) • A + u • A₁) →
  -- Q lies on segment BB₁ (strictly between B and B₁)
  (∃ v : ℝ, 0 < v ∧ v < 1 ∧ Q = (1 - v) • B + v • B₁) →
  -- PQ is parallel to AB
  (P.1 - Q.1) * (B.2 - A.2) = (P.2 - Q.2) * (B.1 - A.1) →
  -- P₁ lies on line PB₁ such that B₁ is strictly between P and P₁
  (∃ w : ℝ, w < 0 ∧ P₁ = (1 - w) • P + w • B₁) →
  -- ∠PP₁C = ∠BAC (angle at P₁ equals angle at A)
  let v1 := P - P₁
  let v2 := C - P₁
  let v3 := B - A
  let v4 := C - A
  (v1.1 * v2.2 - v1.2 * v2.1) * (v3.1 * v4.2 - v3.2 * v4.1) > 0 ∧
  (v1.1 * v2.2 - v1.2 * v2.1) / (‖v1‖ * ‖v2‖) = (v3.1 * v4.2 - v3.2 * v4.1) / (‖v3‖ * ‖v4‖) →
  -- Q₁ lies on line QA₁ such that A₁ is strictly between Q and Q₁
  (∃ z : ℝ, z < 0 ∧ Q₁ = (1 - z) • Q + z • A₁) →
  -- ∠CQ₁Q = ∠CBA (angle at Q₁ equals angle at B)
  let v5 := C - Q₁
  let v6 := Q - Q₁
  let v7 := C - B
  let v8 := A - B
  (v5.1 * v6.2 - v5.2 * v6.1) * (v7.1 * v8.2 - v7.2 * v8.1) > 0 ∧
  (v5.1 * v6.2 - v5.2 * v6.1) / (‖v5‖ * ‖v6‖) = (v7.1 * v8.2 - v7.2 * v8.1) / (‖v7‖ * ‖v8‖) →
  -- P, Q, P₁, Q₁ are concyclic
  ∃ center : ℝ × ℝ, ∃ radius : ℝ,
    radius > 0 ∧
    ‖P - center‖ = radius ∧
    ‖Q - center‖ = radius ∧
    ‖P₁ - center‖ = radius ∧
    ‖Q₁ - center‖ = radius
  := by
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
  -- not proved: the candidate antecedent is vacuous because its first signed-angle orientation contradicts w < 0, so it provides no information from which to derive the genuine coordinate-free theorem
  sorry
