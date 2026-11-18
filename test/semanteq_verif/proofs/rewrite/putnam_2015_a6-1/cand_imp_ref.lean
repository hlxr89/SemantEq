import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (n : ℕ) (hn : 0 < n) 
  (A B M : Matrix (Fin n) (Fin n) ℝ) 
  (h_comm : A * M = M * B)
  (h_charpoly : Matrix.charpoly A = Matrix.charpoly B)
  (X : Matrix (Fin n) (Fin n) ℝ) :
  Matrix.det (A - M * X) = Matrix.det (B - X * M) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_2015_a6
(n : ℕ)
(A B M : Matrix (Fin n) (Fin n) ℝ)
(npos : n > 0)
(hmul : A * M = M * B)
(hpoly : Matrix.charpoly A = Matrix.charpoly B)
: ∀ X : Matrix (Fin n) (Fin n) ℝ, (A - M * X).det = (B - X * M).det :=
by
  intro X
  exact problem_statement_assumed n npos A B M hmul hpoly X
