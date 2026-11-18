import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev S := Finset.Icc 1 1000000

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  ∀ (A : Finset ℕ),
    A ⊆ Finset.Icc 1 (10^6) →
    A.card = 101 →
    ∃ (t : Fin 100 → ℕ),
      (∀ i, t i ∈ Finset.Icc 1 (10^6)) ∧
      (∀ i j : Fin 100, i ≠ j → Disjoint (Finset.image (fun x => x + t i) A) (Finset.image (fun x => x + t j) A)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2003_p1 (A : Finset ℕ) (AS : A ⊆ S) (Acard : A.card = 101) :
    ∃ t ⊆ S, t.card = 100 ∧ ∀ x ∈ t, ∀ y ∈ t, x ≠ y → Disjoint {x + a | a ∈ A} {y + a | a ∈ A} := by
  obtain ⟨t, htS, hdisjoint⟩ := problem_statement_assumed A (by simpa [S] using AS) Acard
  have hAne : A.Nonempty := Finset.card_ne_zero.mp (by omega)
  have htinj : Function.Injective t := by
    intro i j hij
    by_contra hne
    obtain ⟨a, ha⟩ := hAne
    have hd := hdisjoint i j hne
    rw [Finset.disjoint_left] at hd
    have hamem : a + t i ∈ Finset.image (fun x => x + t i) A := Finset.mem_image.mpr ⟨a, ha, rfl⟩
    have hjmem : a + t i ∈ Finset.image (fun x => x + t j) A := by
      exact Finset.mem_image.mpr ⟨a, ha, by simp [hij]⟩
    exact (hd hamem) hjmem
  let u := Finset.univ.image t
  refine ⟨u, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    simpa [S] using htS i
  · simpa [u] using Finset.card_image_of_injective Finset.univ htinj
  · intro x hx y hy hxy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
    have hij : i ≠ j := fun h => hxy (congrArg t h)
    have hd := hdisjoint i j hij
    rw [Finset.disjoint_left] at hd
    rw [Set.disjoint_left]
    intro z hzi hzj
    apply hd
    · obtain ⟨a, ha, haz⟩ := hzi
      exact Finset.mem_image.mpr ⟨a, ha, by simpa [Nat.add_comm] using haz⟩
    · obtain ⟨a, ha, haz⟩ := hzj
      exact Finset.mem_image.mpr ⟨a, ha, by simpa [Nat.add_comm] using haz⟩
