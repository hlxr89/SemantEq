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
  have AS' : ∀ x ∈ A, 1 ≤ x ∧ x ≤ 1000000 := by
    intro x hx
    exact Finset.mem_Icc.mp (AS hx)
  obtain ⟨t, htS, hdis⟩ := problem_statement_assumed A Acard AS'
  have hA : A.Nonempty := by
    apply Finset.card_ne_zero.mp
    rw [Acard]
    exact Nat.succ_ne_zero 100
  have htinj : Function.Injective t := by
    intro i j htij
    by_contra hij -- non-rewrite step
    obtain ⟨a, ha⟩ := hA
    have hamem : a + t i ∈ (Finset.image (fun x => x + t i) A) ∩
        (Finset.image (fun x => x + t j) A) := by
      apply Finset.mem_inter.mpr
      constructor
      · exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
      · exact Finset.mem_image.mpr ⟨a, ha, by rw [htij]⟩
    rw [hdis i j hij] at hamem
    simpa only [Finset.notMem_empty] using hamem
  let e : Fin 100 ↪ ℕ := ⟨t, htinj⟩
  refine ⟨Finset.univ.map e, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_Icc.mpr (htS i)
  · rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
  · intro x hx y hy hxy
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hy
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    obtain ⟨a, ha, hza⟩ := hzi
    obtain ⟨b, hb, hzb⟩ := hzj
    change t i + a = z at hza
    change t j + b = z at hzb
    have hzmem : z ∈ (Finset.image (fun a => a + t i) A) ∩
        (Finset.image (fun a => a + t j) A) := by
      apply Finset.mem_inter.mpr
      constructor
      · exact Finset.mem_image.mpr ⟨a, ha, by rw [← hza, add_comm]⟩
      · exact Finset.mem_image.mpr ⟨b, hb, by rw [← hzb, add_comm]⟩
    rw [hdis i j (by
      intro hij
      apply hxy
      exact congrArg e hij)] at hzmem
    simpa only [Finset.notMem_empty] using hzmem
