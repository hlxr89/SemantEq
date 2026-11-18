import Mathlib

open Nat Set MeasureTheory Topology Filter

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (p : ℤ) (hp : p > 1) 
  (h_prime : ∀ x : ℤ, 0 < x ∧ x < p → Nat.Prime (Int.natAbs (x^2 - x + p))) :
  ∃! triple : ℤ × ℤ × ℤ, 
    let (a, b, c) := triple
    b^2 - 4*a*c = 1 - 4*p ∧ 0 < a ∧ a ≤ c ∧ -a ≤ b ∧ b < a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1973_b3
(p : ℕ)
(pgt1 : p > 1)
(hprime : ∀ x ∈ Set.Ico 0 p, Nat.Prime (x^2 - x + p))
: ∃! triple : ℤ × ℤ × ℤ, let (a,b,c) := triple; b^2 - 4*a*c = 1 - 4*p ∧ 0 < a ∧ a ≤ c ∧ -a ≤ b ∧ b < a := by
  have hpInt : (p : ℤ) > 1 := by exact_mod_cast pgt1
  have hPrimeInt : ∀ x : ℤ, 0 < x ∧ x < (p : ℤ) →
      Nat.Prime (Int.natAbs (x^2 - x + (p : ℤ))) := by
    intro x hx
    have hx0 : 0 ≤ x := by omega
    have habs : (x.natAbs : ℤ) = x := by
      simp [Int.natAbs_of_nonneg hx0]
    have hnlt : x.natAbs < p := by
      exact_mod_cast (show (x.natAbs : ℤ) < (p : ℤ) by simpa [habs] using hx.2)
    have h := hprime x.natAbs ⟨Nat.zero_le _, hnlt⟩
    have hnpos : 0 < x.natAbs := by
      exact_mod_cast (show (0 : ℤ) < (x.natAbs : ℤ) by simpa [habs] using hx.1)
    have hnle : x.natAbs ≤ x.natAbs ^ 2 := by nlinarith
    have hnonneg : 0 ≤ x^2 - x + (p : ℤ) := by nlinarith
    have heq : Int.natAbs (x^2 - x + (p : ℤ)) =
        x.natAbs^2 - x.natAbs + p := by
      apply Int.ofNat_injective
      calc
        Int.ofNat (Int.natAbs (x^2 - x + (p : ℤ))) =
            x^2 - x + (p : ℤ) := Int.natAbs_of_nonneg hnonneg
        _ = Int.ofNat (x.natAbs^2 - x.natAbs + p) := by
          change x^2 - x + (p : ℤ) =
            ((x.natAbs^2 - x.natAbs + p : ℕ) : ℤ)
          push_cast [Nat.cast_sub hnle]
          rw [abs_of_nonneg hx0]
    simpa [heq] using h
  have h := problem_statement_assumed (p : ℤ) hpInt hPrimeInt
  simpa using h
