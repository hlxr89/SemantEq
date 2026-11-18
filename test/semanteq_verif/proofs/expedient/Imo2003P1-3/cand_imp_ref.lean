import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev S := Finset.Icc 1 1000000

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  ∀ (A : Finset ℕ), A.card = 101 →
  (∀ x ∈ A, 1 ≤ x ∧ x ≤ 1000000) →
  ∃ (t : Fin 100 → ℕ),
    (∀ i, 1 ≤ t i ∧ t i ≤ 1000000) ∧
    (∀ i j : Fin 100, i ≠ j → 
      Disjoint {x + t i | x ∈ A} {x + t j | x ∈ A}) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2003_p1 (A : Finset ℕ) (AS : A ⊆ S) (Acard : A.card = 101) :
    ∃ t ⊆ S, t.card = 100 ∧ ∀ x ∈ t, ∀ y ∈ t, x ≠ y → Disjoint {x + a | a ∈ A} {y + a | a ∈ A} := by
  have hA : ∀ x ∈ A, 1 ≤ x ∧ x ≤ 1000000 := by
    intro x hx
    exact Finset.mem_Icc.mp (AS hx)
  obtain ⟨f, hfS, hdisj⟩ := problem_statement_assumed A Acard hA
  have hAne : A.Nonempty := by
    exact Finset.card_pos.mp (by omega)
  have hfinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    obtain ⟨a, ha⟩ := hAne
    have hd := hdisj i j hne
    have hm : a + f i ∈ {x + f i | x ∈ A} := by simp [ha]
    have hn : a + f i ∈ {x + f j | x ∈ A} := by simp [ha, hij]
    exact Set.disjoint_left.mp hd hm hn
  let t : Finset ℕ := Finset.univ.image f
  refine ⟨t, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_Icc.mpr (hfS i)
  · rw [show t = Finset.univ.image f by rfl,
        Finset.card_image_of_injective _ hfinj]
    simp
  · intro x hx y hy hxy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
    have hij : i ≠ j := by
      intro h
      apply hxy
      simpa [h]
    simpa [Nat.add_comm] using hdisj i j hij
