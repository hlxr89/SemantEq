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
  obtain ⟨u, huS, hucard, hdisjoint⟩ := imo2003_p1_assumed A AS Acard
  let e : Fin 100 ≃ ↥u :=
    (finCongr hucard.symm).trans (Finset.equivFin u).symm
  refine ⟨fun i => (e i).1, ?_, ?_⟩
  · intro i
    exact huS (e i).2
  · intro i j hij
    have heij : e i ≠ e j := fun h => hij (e.injective h)
    have h := hdisjoint (e i).1 (e i).2 (e j).1 (e j).2
      (fun h => heij (Subtype.ext h))
    apply Finset.disjoint_coe.mp
    simpa only [Finset.coe_image, Nat.add_comm] using h
