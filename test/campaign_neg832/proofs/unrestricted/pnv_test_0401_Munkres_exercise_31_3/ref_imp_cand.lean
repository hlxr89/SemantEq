import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_31_3_assumed {α : Type*} [PartialOrder α]
  [TopologicalSpace α] (h : OrderTopology α) : RegularSpace α := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {S : Type*} [LinearOrder S] [TopologicalSpace S] : ∀ x y : S, x < y → ∃ U : Set S, IsOpen U ∧ x ∈ U ∧ y ∉ U := by
  classical
  letI : PartialOrder (Fin 3) := {
    le a b := a = b ∨ (a = 1 ∧ b = 2)
    lt a b := a = 1 ∧ b = 2
    le_refl a := Or.inl rfl
    le_trans a b c hab hbc := by
      fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all
    lt_iff_le_not_ge a b := by
      fin_cases a <;> fin_cases b <;> simp
    le_antisymm a b hab hba := by
      fin_cases a <;> fin_cases b <;> simp_all
  }
  letI : TopologicalSpace (Fin 3) := Preorder.topology (Fin 3)
  haveI : OrderTopology (Fin 3) := ⟨rfl⟩
  have hreg : RegularSpace (Fin 3) := exercise_31_3_assumed (α := Fin 3) inferInstance
  letI : RegularSpace (Fin 3) := hreg
  have hchar : ∀ (x : Fin 3) (s : Set (Fin 3)), s ∈ nhds x →
      ∃ t ∈ nhds x, IsClosed t ∧ t ⊆ s :=
    ((regularSpace_TFAE (Fin 3)).out 0 3).mp hreg
  have hopen : IsOpen ({2} : Set (Fin 3)) := by
    convert isOpen_Ioi' (1 : Fin 3) using 1
    ext z
    change z = 2 ↔ ((1 : Fin 3) = 1 ∧ z = 2)
    simp
  obtain ⟨t, ht_nhds, ht_closed, ht_sub⟩ := hchar 2 {2} (hopen.mem_nhds (by simp))
  have ht : t = {2} := by
    apply Set.Subset.antisymm ht_sub
    simpa only [Set.singleton_subset_iff] using mem_of_mem_nhds ht_nhds
  have hclosed : IsClosed ({2} : Set (Fin 3)) := ht ▸ ht_closed
  have hcompl : IsOpen (({2} : Set (Fin 3))ᶜ) := hclosed.isOpen_compl
  have htop : (inferInstance : TopologicalSpace (Fin 3)) =
      TopologicalSpace.generateFrom
        {s : Set (Fin 3) | ∃ a : Fin 3, s = Ioi a ∨ s = Iio a} :=
    OrderTopology.topology_eq_generate_intervals
  have hcomplExplicit : @IsOpen (Fin 3) (inferInstance) (({2} : Set (Fin 3))ᶜ) := hcompl
  rw [htop] at hcomplExplicit
  have hcompl' : TopologicalSpace.GenerateOpen
      {s : Set (Fin 3) | ∃ a : Fin 3, s = Ioi a ∨ s = Iio a}
      (({2} : Set (Fin 3))ᶜ) := hcomplExplicit
  have hprop : ∀ u : Set (Fin 3),
      TopologicalSpace.GenerateOpen
        {s : Set (Fin 3) | ∃ a : Fin 3, s = Ioi a ∨ s = Iio a} u →
      (0 : Fin 3) ∈ u → (2 : Fin 3) ∈ u := by
    intro u hu
    induction hu with
    | basic u hu =>
        rintro h0
        rcases hu with ⟨a, rfl | rfl⟩
        · change (a = 1 ∧ (0 : Fin 3) = 2) at h0
          omega
        · change ((0 : Fin 3) = 1 ∧ a = 2) at h0
          omega
    | univ => simp
    | inter u v hu hv ihu ihv =>
        intro h0
        exact ⟨ihu h0.1, ihv h0.2⟩
    | sUnion A hA ih =>
        intro h0
        simp only [Set.mem_sUnion] at h0 ⊢
        obtain ⟨u, huA, h0u⟩ := h0
        exact ⟨u, huA, ih u huA h0u⟩
  have : (2 : Fin 3) ∈ (({2} : Set (Fin 3))ᶜ) := hprop _ hcompl' (by simp)
  simp at this
