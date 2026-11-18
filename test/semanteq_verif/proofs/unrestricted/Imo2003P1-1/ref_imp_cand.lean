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
    exact Finset.mem_Icc.mpr (hA x hx)
  obtain ⟨t, htS, htcard, ht⟩ := imo2003_p1_assumed A AS Acard
  let e : Fin 100 ≃ ↥t := (Finset.equivFinOfCardEq htcard).symm
  refine ⟨fun i => (e i : ℕ), ?_, ?_⟩
  · intro i
    exact Finset.mem_Icc.mp (htS (e i).property)
  · intro i j hij
    apply Finset.disjoint_iff_inter_eq_empty.mp
    rw [← Finset.disjoint_coe]
    have heij : (e i : ℕ) ≠ (e j : ℕ) := by
      intro h
      apply hij
      exact e.injective (Subtype.ext h)
    have hd := ht (e i : ℕ) (e i).property (e j : ℕ) (e j).property heij
    simpa only [Finset.coe_image, Set.image_image, Function.comp_apply, Nat.add_comm] using hd
