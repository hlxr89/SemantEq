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
    simpa [S] using AS hx
  obtain ⟨t, htS, hpair⟩ := problem_statement_assumed A Acard hA
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  have tinj : Function.Injective t := by
    intro i j hij
    by_contra hne
    obtain ⟨a, ha⟩ := hAne
    have hm : a + t i ∈ (Finset.image (fun x => x + t i) A) ∩
        (Finset.image (fun x => x + t j) A) := by
      simp [ha, hij]
    rw [hpair i j hne] at hm
    simp at hm
  refine ⟨Finset.univ.image t, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    simpa [S] using htS i
  · rw [Finset.card_image_of_injective _ tinj]
    simp
  · intro x hx y hy hxy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
    have hij : i ≠ j := fun h => hxy (congrArg t h)
    apply Set.disjoint_left.2
    intro z hzi hzj
    obtain ⟨a, ha, hza⟩ := hzi
    obtain ⟨b, hb, hzb⟩ := hzj
    have hm : z ∈ (Finset.image (fun x => x + t i) A) ∩
        (Finset.image (fun x => x + t j) A) := by
      simp only [Finset.mem_inter, Finset.mem_image]
      constructor
      · exact ⟨a, ha, by simpa [Nat.add_comm] using hza⟩
      · exact ⟨b, hb, by simpa [Nat.add_comm] using hzb⟩
    rw [hpair i j hij] at hm
    simpa using hm
