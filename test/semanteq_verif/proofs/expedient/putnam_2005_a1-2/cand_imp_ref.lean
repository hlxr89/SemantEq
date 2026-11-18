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
  have hm : 0 < n.toNat := by omega
  obtain ⟨S, hpow, hanti, hsum⟩ := problem_statement_assumed n.toNat hm
  let e : Fin S.card ≃ ↥S := S.equivFin.symm
  have hepow (i : Fin S.card) : IsPow23 (e i).1 := hpow (e i).1 (e i).2
  let r : Fin S.card → ℕ := fun i => (hepow i).choose
  let s : Fin S.card → ℕ := fun i => (hepow i).choose_spec.choose
  have hrs (i : Fin S.card) : (e i).1 = 2^(r i) * 3^(s i) :=
    (hepow i).choose_spec.choose_spec
  refine ⟨S.card, fun i => ![r i, s i], ?_, ?_⟩
  · change n = (∑ i : Fin S.card, (2 : ℤ)^(r i) * 3^(s i))
    have henum : ∑ i : Fin S.card, (e i).1 = S.sum id := by
      rw [Equiv.sum_comp e]
      simpa using S.sum_attach id
    have hnat : (∑ i : Fin S.card, 2^(r i) * 3^(s i)) = n.toNat := by
      calc
        _ = ∑ i : Fin S.card, (e i).1 := by
          apply Finset.sum_congr rfl
          intro i hi
          exact (hrs i).symm
        _ = n.toNat := henum.trans hsum
    rw [← Int.toNat_of_nonneg (le_of_lt hn)]
    exact_mod_cast hnat.symm
  · intro i j hij
    change ¬(2^(r i) * 3^(s i) ∣ 2^(r j) * 3^(s j))
    rw [← hrs i, ← hrs j]
    apply hanti (e i).1 (e j).1 (e i).2 (e j).2
    intro heq
    apply hij
    apply e.injective
    exact Subtype.ext heq
