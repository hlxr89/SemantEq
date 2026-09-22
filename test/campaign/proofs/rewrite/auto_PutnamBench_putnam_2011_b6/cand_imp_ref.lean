import Mathlib

open Topology Filter Matrix Set
open Nat

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem putnam_2011_b6_assumed (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    (p + 1) / 2 ≤
      ((Finset.range p).filter
        (fun n => ¬ p ∣ ∑ k ∈ Finset.range p, k ! * n ^ k)).card := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_2011_b6_refs
(p : ℕ)
(hp : Odd p ∧ Nat.Prime p)
: {n ∈ Finset.range p | ¬ p ∣ ∑ k : Finset.range p, Nat.factorial k * n^(k : ℕ)}.card ≥ (p + 1)/2 := by
  have hsum (n : ℕ) :
      (∑ k : Finset.range p, Nat.factorial k * n^(k : ℕ)) =
        ∑ k ∈ Finset.range p, k ! * n ^ k :=
    (Finset.sum_subtype (Finset.range p) (fun _ => Iff.rfl)
      (fun k => Nat.factorial k * n ^ k)).symm
  simpa only [hsum] using putnam_2011_b6_assumed p hp.2 hp.1
