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
  intro A hcard hA
  have hAS : A ⊆ S := by
    intro x hx
    exact Finset.mem_Icc.mpr (hA x hx)
  obtain ⟨u, huS, hucard, hdisj⟩ := imo2003_p1_assumed A hAS hcard
  let e : Fin 100 ≃ {x // x ∈ u} :=
    (Equiv.cast (congrArg Fin hucard.symm)).trans (Finset.equivFin u).symm
  refine ⟨fun i => (e i).1, ?_, ?_⟩
  · intro i
    exact Finset.mem_Icc.mp (huS (e i).2)
  · intro i j hij
    have heij : (e i).1 ≠ (e j).1 := by
      intro h
      apply hij
      exact e.injective (Subtype.ext h)
    simpa [Nat.add_comm] using hdisj (e i).1 (e i).2 (e j).1 (e j).2 heij
