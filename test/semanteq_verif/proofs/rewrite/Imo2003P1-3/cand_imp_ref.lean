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
  have hA : ∀ x ∈ A, 1 ≤ x ∧ x ≤ 1000000 := by
    intro x hx
    exact Finset.mem_Icc.mp (AS hx)
  obtain ⟨t, htS, hdisjoint⟩ := problem_statement_assumed A Acard hA
  have hApos : 0 < A.card := by
    rw [Acard]
    exact Nat.zero_lt_succ 100
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hApos
  have htinj : Function.Injective t := by
    intro i j ht
    by_contra hij -- non-rewrite step
    have hd := hdisjoint i j hij
    have hai : a + t i ∈ {x + t i | x ∈ A} := ⟨a, ha, rfl⟩
    have haj : a + t i ∈ {x + t j | x ∈ A} := ⟨a, ha, by simpa only [ht]⟩
    exact (Set.disjoint_left.mp hd hai) haj
  refine ⟨Finset.image t Finset.univ, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_Icc.mpr (htS i)
  · rw [Finset.card_image_of_injective _ htinj]
    exact Fintype.card_fin 100
  · intro x hx y hy hxy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    have hij : i ≠ j := by
      intro hij
      apply hxy
      simpa only [hij]
    have hd := hdisjoint i j hij
    simpa only [add_comm] using hd
