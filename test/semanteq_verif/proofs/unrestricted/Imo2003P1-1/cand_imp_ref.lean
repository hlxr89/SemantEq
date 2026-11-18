import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev S := Finset.Icc 1 1000000

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  ∀ (A : Finset ℕ), A.card = 101 → (∀ x ∈ A, 1 ≤ x ∧ x ≤ 1000000) →
  ∃ (t : Fin 100 → ℕ), (∀ i, 1 ≤ t i ∧ t i ≤ 1000000) ∧
    (∀ i j : Fin 100, i ≠ j → (Finset.image (fun x => x + t i) A) ∩ (Finset.image (fun x => x + t j) A) = ∅) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2003_p1 (A : Finset ℕ) (AS : A ⊆ S) (Acard : A.card = 101) :
    ∃ t ⊆ S, t.card = 100 ∧ ∀ x ∈ t, ∀ y ∈ t, x ≠ y → Disjoint {x + a | a ∈ A} {y + a | a ∈ A} := by
  have hA : ∀ x ∈ A, 1 ≤ x ∧ x ≤ 1000000 := by
    intro x hx
    exact Finset.mem_Icc.mp (AS hx)
  obtain ⟨t, htS, ht⟩ := problem_statement_assumed A Acard hA
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  have tinj : Function.Injective t := by
    intro i j htij
    by_contra hij
    have hd := ht i j hij
    obtain ⟨a, ha⟩ := hAne
    have hamem : a + t i ∈ Finset.image (fun x => x + t i) A :=
      Finset.mem_image.mpr ⟨a, ha, rfl⟩
    have hajmem : a + t i ∈ Finset.image (fun x => x + t j) A := by
      apply Finset.mem_image.mpr
      exact ⟨a, ha, by simpa [htij]⟩
    have : a + t i ∈ (Finset.image (fun x => x + t i) A) ∩
        (Finset.image (fun x => x + t j) A) := Finset.mem_inter.mpr ⟨hamem, hajmem⟩
    simpa [hd] using this
  refine ⟨Finset.univ.image t, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_Icc.mpr (htS i)
  · rw [Finset.card_image_of_injective Finset.univ tinj]
    exact Fintype.card_fin 100
  · intro x hx y hy hxy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
    have hij : i ≠ j := by
      intro h
      exact hxy (congrArg t h)
    have hd : Disjoint (Finset.image (fun a => a + t i) A)
        (Finset.image (fun a => a + t j) A) :=
      Finset.disjoint_iff_inter_eq_empty.mpr (ht i j hij)
    rw [← Finset.disjoint_coe] at hd
    simpa only [Finset.coe_image, Set.image_image, Function.comp_apply, Nat.add_comm] using hd
