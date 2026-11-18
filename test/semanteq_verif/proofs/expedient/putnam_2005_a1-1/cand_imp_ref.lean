import Mathlib

open Nat

-- ===== unified context (both sides' local defs, merged) =====
/-- Numbers of the form 2^r * 3^s for nonnegative integers r and s -/
def IsPowerOf2And3 (n : ℕ) : Prop :=
  ∃ r s : ℕ, n = 2^r * 3^s

/-- A finite set of numbers where no element divides another -/
def NoElementDividesAnother (S : Finset ℕ) : Prop :=
  ∀ a b : ℕ, a ∈ S → b ∈ S → a ≠ b → ¬(a ∣ b)

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (n : ℕ) (hn : 0 < n) :
  ∃ S : Finset ℕ, S.Nonempty ∧ 
    (∀ x ∈ S, IsPowerOf2And3 x) ∧
    NoElementDividesAnother S ∧
    S.sum id = n := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_2005_a1
: ∀ n : ℤ, n > 0 → (∃ k : ℕ, ∃ a : Fin k → Fin 2 → ℕ, n = ∑ i : Fin k, 2^(a i 0)*3^(a i 1) ∧
(∀ i j : Fin k, i ≠ j → ¬(2^(a i 0)*3^(a i 1) ∣ 2^(a j 0)*3^(a j 1)))) := by
  intro n hn
  have hnt : 0 < n.toNat := by omega
  obtain ⟨S, _, hp, hdiv, hsum⟩ := problem_statement_assumed n.toNat hnt
  let e : Fin S.card ≃ S := (Finset.equivFin S).symm
  have helem : ∀ x : S, IsPowerOf2And3 x := fun x => hp x x.property
  choose r s hrs using helem
  refine ⟨S.card, fun i => ![r (e i), s (e i)], ?_, ?_⟩
  · have henum : ∑ i : Fin S.card, ((e i : S) : ℕ) = S.sum id := by
      rw [Equiv.sum_comp e]
      simpa using Finset.sum_attach S id
    calc
      n = (n.toNat : ℤ) := by omega
      _ = (S.sum id : ℕ) := by rw [hsum]
      _ = ∑ i : Fin S.card, ((e i : S) : ℕ) := by rw [henum]
      _ = ∑ i : Fin S.card, 2 ^ (![r (e i), s (e i)] 0) * 3 ^ (![r (e i), s (e i)] 1) := by
        norm_cast
        apply Finset.sum_congr rfl
        intro i hi
        simpa using hrs (e i)
  · intro i j hij
    have hne : ((e i : S) : ℕ) ≠ (e j : S) := by
      intro h
      apply hij
      exact e.injective (Subtype.ext h)
    simpa [hrs (e i), hrs (e j)] using
      hdiv (e i) (e j) (e i).property (e j).property hne
