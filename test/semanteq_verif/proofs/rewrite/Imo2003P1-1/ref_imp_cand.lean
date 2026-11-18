import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev S := Finset.Icc 1 1000000

-- ===== assumed statement (antecedent) =====
theorem imo2003_p1_assumed (A : Finset ℕ) (AS : A ⊆ S) (Acard : A.card = 101) :
    ∃ t ⊆ S, t.card = 100 ∧ ∀ x ∈ t, ∀ y ∈ t, x ≠ y → Disjoint {x + a | a ∈ A} {y + a | a ∈ A} := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement :
  ∀ (A : Finset ℕ), A.card = 101 → (∀ x ∈ A, 1 ≤ x ∧ x ≤ 1000000) →
  ∃ (t : Fin 100 → ℕ), (∀ i, 1 ≤ t i ∧ t i ≤ 1000000) ∧
    (∀ i j : Fin 100, i ≠ j → (Finset.image (fun x => x + t i) A) ∩ (Finset.image (fun x => x + t j) A) = ∅) := by
  intro A Acard AS
  have AS' : A ⊆ S := by
    intro x hx
    exact Finset.mem_Icc.mpr (AS x hx)
  obtain ⟨t, htS, htcard, hdis⟩ := imo2003_p1_assumed A AS' Acard
  let e : Fin 100 ≃ ↥t := (Finset.equivFinOfCardEq htcard).symm
  refine ⟨fun i => (e i).1, ?_, ?_⟩
  · intro i
    exact Finset.mem_Icc.mp (htS (e i).2)
  · intro i j hij
    rw [← Finset.disjoint_iff_inter_eq_empty]
    apply Finset.disjoint_left.mpr
    intro z hzi hzj
    have hzi' : z ∈ {q | ∃ a ∈ A, (e i).1 + a = q} := by
      obtain ⟨a, ha, haz⟩ := Finset.mem_image.mp hzi
      exact ⟨a, ha, by rw [← haz, add_comm]⟩
    have hzj' : z ∈ {q | ∃ a ∈ A, (e j).1 + a = q} := by
      obtain ⟨a, ha, haz⟩ := Finset.mem_image.mp hzj
      exact ⟨a, ha, by rw [← haz, add_comm]⟩
    exact Set.disjoint_left.mp (hdis (e i).1 (e i).2 (e j).1 (e j).2 (by
      intro h
      apply hij
      exact e.injective (Subtype.ext h))) hzi' hzj'
