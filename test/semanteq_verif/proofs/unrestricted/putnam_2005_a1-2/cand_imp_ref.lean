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
  have hn0 : 0 < n.toNat := by omega
  obtain ⟨S, hpow, hnd, hsum⟩ := problem_statement_assumed n.toNat hn0
  let e : Fin (Fintype.card {x // x ∈ S}) ≃ {x // x ∈ S} :=
    (Fintype.equivFin {x // x ∈ S}).symm
  have hepow : ∀ i : Fin (Fintype.card {x // x ∈ S}), IsPow23 (e i).1 := by
    intro i
    exact hpow (e i).1 (e i).2
  choose r s hrs using hepow
  let a : Fin (Fintype.card {x // x ∈ S}) → Fin 2 → ℕ :=
    fun i j => if j = 0 then r i else s i
  refine ⟨Fintype.card {x // x ∈ S}, a, ?_, ?_⟩
  · have hval : ∀ i : Fin (Fintype.card {x // x ∈ S}),
        2 ^ (a i 0) * 3 ^ (a i 1) = (e i).1 := by
      intro i
      simp [a, hrs i]
    have henum : (∑ i, 2 ^ (a i 0) * 3 ^ (a i 1)) =
        ∑ x : {x // x ∈ S}, x.1 :=
      Fintype.sum_equiv e _ _ hval
    have hsub : (∑ x : {x // x ∈ S}, x.1) = S.sum id := by
      simpa using (Finset.sum_attach S id)
    have hnat : n.toNat = ∑ i, 2 ^ (a i 0) * 3 ^ (a i 1) :=
      hsum.symm.trans (henum.trans hsub).symm
    rw [show n = (n.toNat : ℤ) by omega]
    exact_mod_cast hnat
  · intro i j hij
    have heij : (e i).1 ≠ (e j).1 := by
      intro h
      apply hij
      apply e.injective
      exact Subtype.ext h
    simpa [a, hrs i, hrs j] using hnd (e i).1 (e j).1 (e i).2 (e j).2 heij
