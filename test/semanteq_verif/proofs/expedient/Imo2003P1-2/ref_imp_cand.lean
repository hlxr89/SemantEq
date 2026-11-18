import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev S := Finset.Icc 1 1000000

-- ===== assumed statement (antecedent) =====
theorem imo2003_p1_assumed (A : Finset ℕ) (AS : A ⊆ S) (Acard : A.card = 101) :
    ∃ t ⊆ S, t.card = 100 ∧ ∀ x ∈ t, ∀ y ∈ t, x ≠ y → Disjoint {x + a | a ∈ A} {y + a | a ∈ A} := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement :
  ∀ (A : Finset ℕ),
    A ⊆ Finset.Icc 1 (10^6) →
    A.card = 101 →
    ∃ (t : Fin 100 → ℕ),
      (∀ i, t i ∈ Finset.Icc 1 (10^6)) ∧
      (∀ i j : Fin 100, i ≠ j → Disjoint (Finset.image (fun x => x + t i) A) (Finset.image (fun x => x + t j) A)) := by
  intro A AS Acard
  obtain ⟨u, huS, hucard, hdis⟩ := imo2003_p1_assumed A AS Acard
  let e : Fin 100 ≃ u := (Finset.equivFinOfCardEq hucard).symm
  refine ⟨fun i => (e i : ℕ), ?_, ?_⟩
  · intro i
    exact huS (e i).property
  · intro i j hij
    have hne : (e i : ℕ) ≠ (e j : ℕ) := fun h => hij (e.injective (Subtype.ext h))
    simpa only [Finset.disjoint_left, Set.disjoint_left, Finset.mem_image, add_comm] using
      hdis (e i) (e i).property (e j) (e j).property hne
