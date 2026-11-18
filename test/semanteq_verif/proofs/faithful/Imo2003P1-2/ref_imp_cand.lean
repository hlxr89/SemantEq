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
  obtain ⟨u, huS, hucard, hdisjoint⟩ := imo2003_p1_assumed A (by simpa [S] using AS) Acard
  let e : u ≃ Fin 100 := Finset.equivFinOfCardEq hucard
  let t : Fin 100 → ℕ := fun i => (e.symm i).1
  refine ⟨t, ?_, ?_⟩
  · intro i
    simpa [S] using huS (e.symm i).2
  · intro i j hij
    have hne : (e.symm i).1 ≠ (e.symm j).1 := by
      intro h
      apply hij
      exact e.symm.injective (Subtype.ext h)
    have hd := hdisjoint (e.symm i).1 (e.symm i).2 (e.symm j).1 (e.symm j).2 hne
    rw [Set.disjoint_left] at hd
    rw [Finset.disjoint_left]
    intro z hzi hzj
    apply hd
    · obtain ⟨a, ha, haz⟩ := Finset.mem_image.mp hzi
      exact ⟨a, ha, by simpa [t, Nat.add_comm] using haz⟩
    · obtain ⟨a, ha, haz⟩ := Finset.mem_image.mp hzj
      exact ⟨a, ha, by simpa [t, Nat.add_comm] using haz⟩
