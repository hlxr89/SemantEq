import Mathlib

open Nat

-- ===== unified context (both sides' local defs, merged) =====
def IsPow23 (n : ℕ) : Prop :=
  ∃ r s : ℕ, n = 2^r * 3^s

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (n : ℕ) (hn : 0 < n) :
  ∃ S : Finset ℕ,
    (∀ x ∈ S, IsPow23 x) ∧
    (∀ x y : ℕ, x ∈ S → y ∈ S → x ≠ y → ¬(x ∣ y)) ∧
    S.sum id = n :=
by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_2005_a1
: ∀ n : ℤ, n > 0 → (∃ k : ℕ, ∃ a : Fin k → Fin 2 → ℕ, n = ∑ i : Fin k, 2^(a i 0)*3^(a i 1) ∧
(∀ i j : Fin k, i ≠ j → ¬(2^(a i 0)*3^(a i 1) ∣ 2^(a j 0)*3^(a j 1)))) :=
by
  intro n hn
  have hnNat : 0 < n.toNat := by
    apply Int.natCast_pos.mp
    rw [Int.toNat_of_nonneg (le_of_lt hn)]
    exact hn
  obtain ⟨S, hpow, hanti, hsum⟩ := problem_statement_assumed n.toNat hnNat
  let e : Fin S.card ≃ S := (S.equivFin).symm
  let r : Fin S.card → ℕ := fun i => Classical.choose (hpow (e i) (e i).property)
  let s : Fin S.card → ℕ := fun i => Classical.choose (Classical.choose_spec (hpow (e i) (e i).property))
  let a : Fin S.card → Fin 2 → ℕ := fun i j => Fin.cases (r i) (fun _ => s i) j
  have heach : ∀ i : Fin S.card, (e i : ℕ) = 2 ^ (a i 0) * 3 ^ (a i 1) := by
    intro i
    exact Classical.choose_spec (Classical.choose_spec (hpow (e i) (e i).property))
  refine ⟨S.card, a, ?_, ?_⟩
  · have henum : ∑ i : Fin S.card, (e i : ℕ) = S.sum id := by
      rw [e.sum_comp]
      exact Finset.sum_coe_sort S id
    rw [← Int.toNat_of_nonneg (le_of_lt hn), ← hsum, ← henum]
    exact_mod_cast Finset.sum_congr rfl (fun i _ => heach i)
  · intro i j hij hdiv
    have heij : (e i : ℕ) ≠ (e j : ℕ) := fun h => hij (e.injective (Subtype.ext h))
    apply hanti (e i) (e j) (e i).property (e j).property heij
    rw [heach i, heach j]
    exact_mod_cast hdiv
