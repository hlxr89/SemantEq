import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev S := Finset.Icc 1 1000000

-- ===== assumed statement (antecedent) =====
theorem imo2003_p1_assumed (A : Finset ℕ) (AS : A ⊆ S) (Acard : A.card = 101) :
    ∃ t ⊆ S, t.card = 100 ∧ ∀ x ∈ t, ∀ y ∈ t, x ≠ y → Disjoint {x + a | a ∈ A} {y + a | a ∈ A} := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement :
  ∀ (A : Finset ℕ), A.card = 101 →
  (∀ x ∈ A, 1 ≤ x ∧ x ≤ 1000000) →
  ∃ (t : Fin 100 → ℕ),
    (∀ i, 1 ≤ t i ∧ t i ≤ 1000000) ∧
    (∀ i j : Fin 100, i ≠ j → 
      Disjoint {x + t i | x ∈ A} {x + t j | x ∈ A}) := by
  intro A Acard hA
  have AS : A ⊆ S := by
    intro x hx
    exact Finset.mem_Icc.mpr (hA x hx)
  obtain ⟨u, huS, hucard, hdisjoint⟩ := imo2003_p1_assumed A AS Acard
  let e : Fin 100 ≃o ↥u := u.orderIsoOfFin hucard
  let t : Fin 100 → ℕ := fun i ↦ e i
  refine ⟨t, ?_, ?_⟩
  · intro i
    exact Finset.mem_Icc.mp (huS (e i).property)
  · intro i j hij
    have htij : t i ≠ t j := by
      intro ht
      apply hij
      apply e.injective
      exact Subtype.ext ht
    have hd := hdisjoint (t i) (e i).property (t j) (e j).property htij
    simpa only [add_comm] using hd
