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
  obtain ⟨f, hfS, hdis⟩ := problem_statement_assumed A AS Acard
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hA : A.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨a, ha⟩ := hA
    have hd := Finset.disjoint_left.mp (hdis i j hne)
    exact hd (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
      (Finset.mem_image.mpr ⟨a, ha, by simp [hij]⟩)
  refine ⟨Finset.univ.image f, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact hfS i
  · rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  · intro x hx y hy hxy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
    simpa only [Finset.disjoint_left, Set.disjoint_left, Finset.mem_image, add_comm] using
      hdis i j (fun h => hxy (congrArg f h))
