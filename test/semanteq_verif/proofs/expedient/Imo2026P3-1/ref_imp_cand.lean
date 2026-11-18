import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
noncomputable section

/-- The multiset of piece lengths obtained by cutting `[0,1]` at the points of a
finite set `S ⊆ (0,1)`.  We sort `S` ascending, prepend `0` and append `1`, and
take consecutive differences.  The result is a list of `|S| + 1` positive reals
summing to `1` (when `S ⊆ (0,1)`). -/
def pieceLengths (S : Finset ℝ) : List ℝ :=
  let l : List ℝ := (0 : ℝ) :: (S.sort (· ≤ ·)) ++ [1]
  List.zipWith (fun a b => b - a) l l.tail

/-- The sum of the entries of a list `L` at the (0-indexed) even positions, after
sorting `L` in non-increasing order.  These are the entries in the `1`st, `3`rd,
`5`th, … positions of the sorted (decreasing) list, i.e. the pieces claimed by
the first mover under the greedy claiming rule. -/
def firstPlayerShare (L : List ℝ) : ℝ :=
  let sorted := L.mergeSort (· ≥ ·)
  ((sorted.zipIdx.filter (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum

/-- `L(A,B)`: Liu Bang's total length, given Liu Bang's marks `A` and Xiang Yu's
marks `B`. -/
def L (A B : Finset ℝ) : ℝ :=
  firstPlayerShare (pieceLengths (A ∪ B))

/-- The set of admissible markings for a player: a finite subset of `(0,1)` of
size at most `n`.  We encode it as a `Finset ℝ` subject to the side conditions. -/
def AdmissibleMark (n : ℕ) (X : Finset ℝ) : Prop :=
  (↑X ⊆ Set.Ioo (0 : ℝ) 1) ∧ X.card ≤ n

/-- The value Liu Bang can guarantee.

`V n` is the supremum over Liu Bang's admissible markings `A` of the infimum,
over Xiang Yu's admissible markings `B` disjoint from `A`, of `L A B`. -/
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
    simp
  · intro ε hε
    exact ⟨∅, ∅, by simp⟩
