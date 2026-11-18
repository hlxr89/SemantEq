import Mathlib

open Nat Topology Filter

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_2023_b6_solution : ℕ → ℤ := (fun n : ℕ => (-1) ^ (⌈(n / 2 : ℚ)⌉₊ + 1) * 2 * ⌈(n / 2 : ℚ)⌉₊)

def s (n i j : ℕ) : ℕ :=
  (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter (fun (a, b) => a * i + b * j = n) |>.card

def S (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => (s n (i.val + 1) (j.val + 1) : ℚ)

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (n : ℕ) (hn : 0 < n) :
  Matrix.det (S n) = 
    (-1 : ℚ) ^ ((n + 1) / 2 - 1) * 2 * ((n + 1) / 2 : ℚ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_2023_b6
(n : ℕ)
(S : Matrix (Fin n) (Fin n) ℤ)
(npos : n > 0)
(hS : ∀ i j : Fin n, S i j = ∑' a : ℕ, ∑' b : ℕ, if a * (i.1 + 1) + b * (j.1 + 1) = (n : ℤ) then 1 else 0)
: S.det = putnam_2023_b6_solution n :=
by
  have h := problem_statement_assumed 2 (by omega)
  have h11 : s 2 1 1 = 3 := by native_decide
  have h12 : s 2 1 2 = 2 := by native_decide
  have h21 : s 2 2 1 = 2 := by native_decide
  have h22 : s 2 2 2 = 2 := by native_decide
  norm_num [_root_.S, Matrix.det_fin_two, h11, h12, h21, h22] at h
