import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

namespace Erdos689

-- ===== assumed statement (antecedent) =====
theorem erdos_689_assumed :
    ∀ n ≥ 3, ∃ a : ℕ → ℕ, ∀ m ∈ Finset.Icc 1 n,
      2 ≤ (Finset.Icc 1 n |>.filter fun p => p.Prime ∧ a p ≡ m [MOD p]).card := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_689_goal :
    ∀ᶠ n in .atTop, ∃ a : ℕ → ℕ, ∀ m ∈ Finset.Icc 1 n,
      2 ≤ (Finset.Icc 1 n |>.filter fun p => p.Prime ∧ a p ≡ m [MOD p]).card := by
  exfalso
  obtain ⟨a, ha⟩ := erdos_689_assumed 3 (by norm_num)
  have mem_two_of_card_two {m : ℕ}
      (hcard : 2 ≤ (Finset.Icc 1 3 |>.filter fun p => p.Prime ∧ a p ≡ m [MOD p]).card) :
      2 ∈ (Finset.Icc 1 3 |>.filter fun p => p.Prime ∧ a p ≡ m [MOD p]) := by
    by_contra htwo
    have hsub :
        (Finset.Icc 1 3 |>.filter fun p => p.Prime ∧ a p ≡ m [MOD p]) ⊆ {3} := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Icc] at hp
      rcases hp with ⟨⟨hp1, hp3⟩, hprime, hmod⟩
      have hpne : p ≠ 1 := hprime.ne_one
      have : p = 2 ∨ p = 3 := by omega
      rcases this with rfl | rfl
      · exfalso
        apply htwo
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hprime, hmod⟩
      · simp
    have hc := Finset.card_le_card hsub
    simp at hc
    omega
  have hmem1 : 1 ∈ Finset.Icc 1 3 := by simp
  have hmem2 : 2 ∈ Finset.Icc 1 3 := by simp
  have hcard1 := ha 1 hmem1
  have hcard2 := ha 2 hmem2
  have htwo1 := mem_two_of_card_two hcard1
  have htwo2 := mem_two_of_card_two hcard2
  simp only [Finset.mem_filter] at htwo1 htwo2
  have hbad : 1 ≡ 2 [MOD 2] := htwo1.2.2.symm.trans htwo2.2.2
  norm_num [Nat.ModEq] at hbad

end Erdos689
