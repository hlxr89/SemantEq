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
  obtain ⟨u, huS, hucard, hdisjoint⟩ := imo2003_p1_assumed A AS Acard
  let e : Fin 100 ≃ ↥u := (Finset.equivFinOfCardEq hucard).symm
  let t : Fin 100 → ℕ := fun i => e i
  refine ⟨t, ?_, ?_⟩
  · intro i
    simpa [S, t] using huS (e i).property
  · intro i j hij
    have htne : t i ≠ t j := by
      intro heq
      apply hij
      apply e.injective
      exact Subtype.ext heq
    have hd := hdisjoint (t i) (e i).property (t j) (e j).property htne
    apply Finset.disjoint_iff_inter_eq_empty.mp
    apply Finset.disjoint_left.mpr
    intro z hzi hzj
    obtain ⟨a, ha, haz⟩ := Finset.mem_image.mp hzi
    obtain ⟨b, hb, hbz⟩ := Finset.mem_image.mp hzj
    exact Set.disjoint_left.mp hd
      ⟨a, ha, (Nat.add_comm (t i) a).trans haz⟩
      ⟨b, hb, (Nat.add_comm (t j) b).trans hbz⟩
