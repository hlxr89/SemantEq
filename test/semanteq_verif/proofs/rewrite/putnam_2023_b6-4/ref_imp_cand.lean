import Mathlib

open Nat Topology Filter

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_2023_b6_solution : ℕ → ℤ := (fun n : ℕ => (-1) ^ (⌈(n / 2 : ℚ)⌉₊ + 1) * 2 * ⌈(n / 2 : ℚ)⌉₊)

def s (n i j : ℕ) : ℕ :=
  (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter (fun (a, b) => a * i + b * j = n) |>.card

def S (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => (s n (i.val + 1) (j.val + 1) : ℚ)

-- ===== assumed statement (antecedent) =====
theorem putnam_2023_b6_assumed
(n : ℕ)
(S : Matrix (Fin n) (Fin n) ℤ)
(npos : n > 0)
(hS : ∀ i j : Fin n, S i j = ∑' a : ℕ, ∑' b : ℕ, if a * (i.1 + 1) + b * (j.1 + 1) = (n : ℤ) then 1 else 0)
: S.det = putnam_2023_b6_solution n :=
by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (n : ℕ) (hn : 0 < n) :
  Matrix.det (S n) = 
    (-1 : ℚ) ^ ((n + 1) / 2 - 1) * 2 * ((n + 1) / 2 : ℚ) := by
  -- not proved: the candidate uses rational division in its final factor and is false at n = 2 (RHS 3, determinant 2)
  sorry
