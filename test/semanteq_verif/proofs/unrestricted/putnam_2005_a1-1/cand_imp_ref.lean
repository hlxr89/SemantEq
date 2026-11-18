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
  have hn_nonneg : 0 ≤ n := le_of_lt hn
  have hn_toNat : 0 < n.toNat := by
    omega
  obtain ⟨S, hS_ne, hpow, hdiv, hsum⟩ := problem_statement_assumed n.toNat hn_toNat
  let e : S ≃ Fin S.card := S.equivFin
  have hexp : ∀ i : Fin S.card, ∃ r s : ℕ, (e.symm i : ℕ) = 2^r * 3^s := by
    intro i
    exact hpow (e.symm i) (e.symm i).property
  choose r s hrs using hexp
  let a : Fin S.card → Fin 2 → ℕ := fun i b => if b = 0 then r i else s i
  have hvalue (i : Fin S.card) : 2^(a i 0) * 3^(a i 1) = (e.symm i : ℕ) := by
    simpa [a] using (hrs i).symm
  have hsum_enum : ∑ i : Fin S.card, (e.symm i : ℕ) = n.toNat := by
    calc
      ∑ i : Fin S.card, (e.symm i : ℕ) = ∑ x : S, (x : ℕ) := Equiv.sum_comp e.symm _
      _ = S.sum id := by
        simpa [id] using (Finset.sum_coe_sort S (fun x : ℕ => x))
      _ = n.toNat := hsum
  have hsum_powers : ∑ i : Fin S.card, 2^(a i 0) * 3^(a i 1) = n.toNat := by
    calc
      ∑ i : Fin S.card, 2^(a i 0) * 3^(a i 1) = ∑ i : Fin S.card, (e.symm i : ℕ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hvalue i
      _ = n.toNat := hsum_enum
  refine ⟨S.card, a, ?_, ?_⟩
  · rw [← Int.toNat_of_nonneg hn_nonneg]
    exact_mod_cast hsum_powers.symm
  · intro i j hij
    rw [hvalue i, hvalue j]
    apply hdiv (e.symm i) (e.symm j) (e.symm i).property (e.symm j).property
    intro hval
    apply hij
    apply e.symm.injective
    exact Subtype.ext hval
