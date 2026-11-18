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
  classical
  intro n hn
  have hn_nonneg : 0 ≤ n := le_of_lt hn
  have hn_nat : 0 < n.toNat := by
    apply Int.natCast_pos.mp
    rw [Int.toNat_of_nonneg hn_nonneg]
    exact hn
  obtain ⟨S, hS_nonempty, hpower, hndiv, hsum⟩ :=
    problem_statement_assumed n.toNat hn_nat
  let e : Fin S.card ≃ ↥S := S.equivFin.symm
  have he_power (i : Fin S.card) : IsPowerOf2And3 (e i : ℕ) :=
    hpower (e i : ℕ) (e i).property
  let r : Fin S.card → ℕ := fun i => (he_power i).choose
  let s : Fin S.card → ℕ := fun i => (he_power i).choose_spec.choose
  have hrs (i : Fin S.card) : (e i : ℕ) = 2^(r i) * 3^(s i) :=
    (he_power i).choose_spec.choose_spec
  let a : Fin S.card → Fin 2 → ℕ := fun i => ![r i, s i]
  refine ⟨S.card, a, ?_, ?_⟩
  · have hindexed : ∑ i : Fin S.card, (e i : ℕ) = n.toNat := by
      rw [Equiv.sum_comp e (fun x : ↥S => (x : ℕ))]
      rw [Finset.sum_coe_sort S (fun x : ℕ => x)]
      exact hsum
    have hgoal_nat : n.toNat = ∑ i : Fin S.card, 2^(a i 0)*3^(a i 1) := by
      rw [← hindexed]
      congr 1
      funext i
      simpa only [a, Matrix.cons_val_zero, Matrix.cons_val_one] using hrs i
    rw [← Int.toNat_of_nonneg hn_nonneg]
    exact_mod_cast hgoal_nat
  · intro i j hij
    have he_ne : (e i : ℕ) ≠ (e j : ℕ) := by
      intro heq
      apply hij
      apply e.injective
      exact Subtype.ext heq
    have hnot := hndiv (e i : ℕ) (e j : ℕ) (e i).property (e j).property he_ne
    simpa only [a, Matrix.cons_val_zero, Matrix.cons_val_one, ← hrs i, ← hrs j] using hnot
