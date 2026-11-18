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
  intro A Acard hA
  have AS : A ⊆ S := by
    intro x hx
    simpa [S] using hA x hx
  obtain ⟨T, hTS, hTcard, hdis⟩ := imo2003_p1_assumed A AS Acard
  let e : ↥T ≃ Fin 100 := Finset.equivFinOfCardEq hTcard
  refine ⟨fun i => e.symm i, ?_, ?_⟩
  · intro i
    simpa [S] using hTS (e.symm i).property
  · intro i j hij
    have hne : (e.symm i : ℕ) ≠ e.symm j := by
      intro h
      apply hij
      exact e.symm.injective (Subtype.ext h)
    have hd := hdis (e.symm i) (e.symm i).property
      (e.symm j) (e.symm j).property hne
    apply Finset.disjoint_iff_inter_eq_empty.mp
    apply Finset.disjoint_left.2
    intro z hzi hzj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hzi
    obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp hzj
    apply (Set.disjoint_left.1 hd) (by
      exact ⟨a, ha, Nat.add_comm (e.symm i) a⟩)
    exact ⟨b, hb, by simpa [Nat.add_comm] using hab⟩
