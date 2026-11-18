import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev S := Finset.Icc 1 1000000

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  ∀ (A : Finset ℕ), A.card = 101 → (∀ x ∈ A, 1 ≤ x ∧ x ≤ 1000000) →
  ∃ (t : Fin 100 → ℕ), (∀ i, 1 ≤ t i ∧ t i ≤ 1000000) ∧
    (∀ i j : Fin 100, i ≠ j → (Finset.image (fun x => x + t i) A) ∩ (Finset.image (fun x => x + t j) A) = ∅) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2003_p1 (A : Finset ℕ) (AS : A ⊆ S) (Acard : A.card = 101) :
    ∃ t ⊆ S, t.card = 100 ∧ ∀ x ∈ t, ∀ y ∈ t, x ≠ y → Disjoint {x + a | a ∈ A} {y + a | a ∈ A} := by
  have hA : ∀ x ∈ A, 1 ≤ x ∧ x ≤ 1000000 := by
    intro x hx
    simpa [S] using AS hx
  obtain ⟨f, hfS, hpair⟩ := problem_statement_assumed A Acard hA
  have hfinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hinter := hpair i j hne
    have himage : Finset.image (fun x => x + f i) A = ∅ := by
      simpa [hij] using hinter
    have hAempty : A = ∅ := Finset.image_eq_empty.mp himage
    simp [hAempty] at Acard
  let t : Finset ℕ := Finset.image f Finset.univ
  refine ⟨t, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    simpa [S] using hfS i
  · simp [t, Finset.card_image_of_injective _ hfinj]
  · intro x hx y hy hxy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    have hij : i ≠ j := by
      intro heq
      apply hxy
      exact congrArg f heq
    have hd : Disjoint (Finset.image (fun a => a + f i) A)
        (Finset.image (fun a => a + f j) A) :=
      Finset.disjoint_iff_inter_eq_empty.mpr (hpair i j hij)
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    obtain ⟨a, ha, haz⟩ := hzi
    obtain ⟨b, hb, hbz⟩ := hzj
    apply (Finset.disjoint_left.mp hd) (Finset.mem_image.mpr
      ⟨a, ha, (Nat.add_comm a (f i)).trans haz⟩)
    exact Finset.mem_image.mpr ⟨b, hb, (Nat.add_comm b (f j)).trans hbz⟩
