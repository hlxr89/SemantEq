import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev S := Finset.Icc 1 1000000

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  ∀ (A : Finset ℕ),
    A ⊆ Finset.Icc 1 (10^6) →
    A.card = 101 →
    ∃ (t : Fin 100 → ℕ),
      (∀ i, t i ∈ Finset.Icc 1 (10^6)) ∧
      (∀ i j : Fin 100, i ≠ j → Disjoint (Finset.image (fun x => x + t i) A) (Finset.image (fun x => x + t j) A)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2003_p1 (A : Finset ℕ) (AS : A ⊆ S) (Acard : A.card = 101) :
    ∃ t ⊆ S, t.card = 100 ∧ ∀ x ∈ t, ∀ y ∈ t, x ≠ y → Disjoint {x + a | a ∈ A} {y + a | a ∈ A} := by
  obtain ⟨t, htS, hdisjoint⟩ := problem_statement_assumed A AS Acard
  have hAne : A.Nonempty := Finset.card_ne_zero.mp fun h =>
    Nat.noConfusion (Acard.symm.trans h)
  have htinj : Function.Injective t := by
    intro i j htij
    apply Classical.byContradiction -- non-rewrite step
    intro hij
    obtain ⟨a, ha⟩ := hAne
    have hd := hdisjoint i j hij
    rw [htij] at hd
    have hamem : a + t j ∈ Finset.image (fun x => x + t j) A :=
      Finset.mem_image.mpr ⟨a, ha, rfl⟩
    exact (Finset.disjoint_left.mp hd) hamem hamem
  refine ⟨Finset.univ.image t, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact htS i
  · rw [Finset.card_image_of_injective Finset.univ htinj]
    exact Finset.card_fin 100
  · intro x hx y hy hxy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
    have hij : i ≠ j := fun h => hxy (congrArg t h)
    have hd := hdisjoint i j hij
    simpa only [Finset.coe_image, Nat.add_comm] using (Finset.disjoint_coe.mpr hd)
