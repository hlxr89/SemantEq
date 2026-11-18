import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev S := Finset.Icc 1 1000000

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  ∀ (A : Finset ℕ), A.card = 101 →
  (∀ x ∈ A, 1 ≤ x ∧ x ≤ 1000000) →
  ∃ (t : Fin 100 → ℕ),
    (∀ i, 1 ≤ t i ∧ t i ≤ 1000000) ∧
    (∀ i j : Fin 100, i ≠ j → 
      Disjoint {x + t i | x ∈ A} {x + t j | x ∈ A}) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2003_p1 (A : Finset ℕ) (AS : A ⊆ S) (Acard : A.card = 101) :
    ∃ t ⊆ S, t.card = 100 ∧ ∀ x ∈ t, ∀ y ∈ t, x ≠ y → Disjoint {x + a | a ∈ A} {y + a | a ∈ A} := by
  have AS' : ∀ x ∈ A, 1 ≤ x ∧ x ≤ 1000000 := by
    intro x hx
    simpa [S] using AS hx
  obtain ⟨u, huS, hdisj⟩ := problem_statement_assumed A Acard AS'
  have hu_injective : Function.Injective u := by
    intro i j hij
    apply not_ne_iff.mp
    intro hne
    have hd := hdisj i j hne
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
    have hmem_i : a + u i ∈ {x + u i | x ∈ A} := ⟨a, ha, rfl⟩
    have hmem_j : a + u i ∈ {x + u j | x ∈ A} := by
      exact ⟨a, ha, by simp [hij]⟩
    exact Set.disjoint_left.mp hd hmem_i hmem_j
  refine ⟨Finset.univ.image u, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    simpa [S] using huS i
  · rw [Finset.card_image_of_injective Finset.univ hu_injective]
    exact Finset.card_fin 100
  · intro x hx y hy hxy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
    have hij : i ≠ j := by
      intro h
      apply hxy
      simp [h]
    simpa [add_comm] using hdisj i j hij
