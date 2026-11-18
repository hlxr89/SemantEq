import Mathlib

open Topology Filter Set Polynomial Function

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_1981_b4_solution : Prop := False

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed : ∃ (V : Set (Matrix (Fin 5) (Fin 7) ℝ)),
    (∀ (A B : Matrix (Fin 5) (Fin 7) ℝ) (r s : ℝ), A ∈ V → B ∈ V → r • A + s • B ∈ V) ∧
    (∃ (A : Matrix (Fin 5) (Fin 7) ℝ), A ∈ V ∧ Matrix.rank A = 0) ∧
    (∃ (A : Matrix (Fin 5) (Fin 7) ℝ), A ∈ V ∧ Matrix.rank A = 1) ∧
    (∃ (A : Matrix (Fin 5) (Fin 7) ℝ), A ∈ V ∧ Matrix.rank A = 2) ∧
    (∃ (A : Matrix (Fin 5) (Fin 7) ℝ), A ∈ V ∧ Matrix.rank A = 4) ∧
    (∃ (A : Matrix (Fin 5) (Fin 7) ℝ), A ∈ V ∧ Matrix.rank A = 5) ∧
    (¬ ∃ (A : Matrix (Fin 5) (Fin 7) ℝ), A ∈ V ∧ Matrix.rank A = 3) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1981_b4
    (VAB : Set (Matrix (Fin 5) (Fin 7) ℝ) → Prop)
    (Vrank : Set (Matrix (Fin 5) (Fin 7) ℝ) → ℕ → Prop)
    (hVAB : ∀ V, VAB V = (∀ A ∈ V, ∀ B ∈ V, ∀ r s : ℝ, r • A + s • B ∈ V))
    (hVrank : ∀ V k, Vrank V k = ∃ A ∈ V, A.rank = k) :
    putnam_1981_b4_solution ↔
    (∀ V,
      VAB V → Vrank V 0 → Vrank V 1 →
      Vrank V 2 → Vrank V 4 → Vrank V 5 →
    Vrank V 3) := by
  constructor
  · intro hfalse
    exact False.elim hfalse
  · intro hall
    obtain ⟨V, hclosed, h0, h1, h2, h4, h5, hnot3⟩ := problem_statement_assumed
    have hvab : VAB V := by
      rw [hVAB]
      intro A hA B hB r s
      exact hclosed A B r s hA hB
    have hrank0 : Vrank V 0 := by
      rw [hVrank]
      exact h0
    have hrank1 : Vrank V 1 := by
      rw [hVrank]
      exact h1
    have hrank2 : Vrank V 2 := by
      rw [hVrank]
      exact h2
    have hrank4 : Vrank V 4 := by
      rw [hVrank]
      exact h4
    have hrank5 : Vrank V 5 := by
      rw [hVrank]
      exact h5
    have hrank3 := hall V hvab hrank0 hrank1 hrank2 hrank4 hrank5
    rw [hVrank] at hrank3
    exact hnot3 hrank3
