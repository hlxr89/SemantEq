import Mathlib

open Nat

namespace Imo1960P1

-- ===== unified context (both sides' local defs, merged) =====
def sumOfSquares (L : List ℕ) : ℕ :=
  (L.map fun x => x * x).sum

def ProblemPredicate (n : ℕ) : Prop :=
  (Nat.digits 10 n).length = 3 ∧ 11 ∣ n ∧ n / 11 = sumOfSquares (Nat.digits 10 n)

def SolutionPredicate (n : ℕ) : Prop :=
  n = 550 ∨ n = 803

-- ===== assumed statement (antecedent) =====
theorem imo1960_p1_alt_assumed (n : ℕ) :
    (ProblemPredicate n → SolutionPredicate n) ∧ (SolutionPredicate n → ProblemPredicate n) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1960_p1 (n : ℕ) : ProblemPredicate n ↔ SolutionPredicate n := by
  exact ⟨(imo1960_p1_alt_assumed n).1, (imo1960_p1_alt_assumed n).2⟩

end Imo1960P1
