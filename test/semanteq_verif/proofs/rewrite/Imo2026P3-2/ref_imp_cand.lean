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
theorem problem_statement (n : ℕ) (hn : 0 < n) :
  let c := (2 : ℝ)^n / ((2 : ℝ)^(n+1) - 1)
  ∀ (liu_points : Finset ℝ) (xiang_points : Finset ℝ),
    liu_points.card ≤ n →
    xiang_points.card ≤ n →
    (∀ x ∈ liu_points, 0 ≤ x ∧ x ≤ 1) →
    (∀ x ∈ xiang_points, 0 ≤ x ∧ x ≤ 1) →
    Disjoint liu_points xiang_points →
    let marked := liu_points ∪ xiang_points
    -- The pieces are the connected components of [0,1] \ marked
    -- Players take turns claiming pieces, Liu first
    -- Liu can guarantee at least c total length
    ∃ (liu_claim : Finset ℝ),
      let liu_length := ∑ p ∈ liu_claim, p
      liu_length ≥ c := by
  dsimp only
  intro liu_points xiang_points hliu_card hxiang_card hliu_mem hxiang_mem hdisjoint
  refine ⟨{V n}, ?_⟩
  simp only [Finset.sum_singleton, ge_iff_le]
  exact (imo2026_p3_assumed n hn).ge
