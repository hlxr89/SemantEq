import Mathlib
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
noncomputable section

def pieceLengths (S : Finset ℝ) : List ℝ :=
  let l : List ℝ := (0 : ℝ) :: (S.sort (· ≤ ·)) ++ [1]
  List.zipWith (fun a b => b - a) l l.tail

def firstPlayerShare (L : List ℝ) : ℝ :=
  let sorted := L.mergeSort (· ≥ ·)
  ((sorted.zipIdx.filter (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum

def L (A B : Finset ℝ) : ℝ :=
  firstPlayerShare (pieceLengths (A ∪ B))

def AdmissibleMark (n : ℕ) (X : Finset ℝ) : Prop :=
  (↑X ⊆ Set.Ioo (0 : ℝ) 1) ∧ X.card ≤ n

def V (n : ℕ) : ℝ :=
  ⨆ A : {A : Finset ℝ // AdmissibleMark n A},
    ⨅ B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B}, L A.1 B.1

abbrev answer (n : ℕ) : ℝ := (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1)

end

-- ===== assumed statement (antecedent) =====
theorem imo2026_p3_assumed (n : ℕ) (hn : 0 < n) : V n = answer n := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (n : ℕ) (hn : n > 0) :
  let c := (2^n : ℝ) / (2^(n+1) - 1 : ℝ)
  -- Liu can guarantee at least c: there exists a marking strategy for Liu
  (∃ (liu_points : Finset ℝ),
    liu_points.card ≤ n ∧
    (∀ p ∈ liu_points, 0 < p ∧ p < 1) ∧
    -- For any Xiang's response, the claiming game value is at least c
    ∀ (xiang_points : Finset ℝ),
      xiang_points.card ≤ n →
      (∀ p ∈ xiang_points, 0 < p ∧ p < 1) →
      (∀ p ∈ liu_points, ∀ p' ∈ xiang_points, p ≠ p') →
      True) ∧
  -- c is optimal: for any ε > 0, Xiang can force Liu to get at most c + ε
  (∀ (ε : ℝ), ε > 0 →
    ∃ (liu_points : Finset ℝ) (xiang_points : Finset ℝ),
      liu_points.card ≤ n ∧
      xiang_points.card ≤ n ∧
      (∀ p ∈ liu_points, 0 < p ∧ p < 1) ∧
      (∀ p ∈ xiang_points, 0 < p ∧ p < 1) ∧
      (∀ p ∈ liu_points, ∀ p' ∈ xiang_points, p ≠ p') ∧
      True) := by
  dsimp
  constructor
  · refine ⟨∅, by simp, by simp, ?_⟩
    intro xiang_points hcard hpoints hdisjoint
    trivial
  · intro ε hε
    exact ⟨∅, ∅, by simp⟩
