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
theorem dummy {X : Type*} [PartialOrder X] [TopologicalSpace X] [OrderTopology X] : ∀ (x : X) (s : Set X), IsOpen s → x ∈ s → ∃ (t : Set X), IsOpen t ∧ x ∈ t ∧ Disjoint t s := by
  classical
  letI : PartialOrder (Fin 3) := {
    le a b := a = b ∨ (a = 0 ∧ b = 1)
    lt a b := (a = b ∨ (a = 0 ∧ b = 1)) ∧ ¬(b = a ∨ (b = 0 ∧ a = 1))
    le_refl a := Or.inl rfl
    le_trans a b c hab hbc := by
      rcases hab with rfl | ⟨ha, hb⟩
      · exact hbc
      rcases hbc with hbc | ⟨hb', hc⟩
      · exact Or.inr ⟨ha, (hb.symm.trans hbc).symm⟩
      · omega
    le_antisymm a b hab hba := by
      rcases hab with hab | ⟨ha, hb⟩
      · exact hab
      rcases hba with hba | ⟨hb', ha'⟩
      · exact hba.symm
      · omega
    lt_iff_le_not_ge a b := Iff.rfl }
  let g : Set (Set (Fin 3)) := {s | ∃ a, s = Ioi a ∨ s = Iio a}
  letI : TopologicalSpace (Fin 3) := generateFrom g
  letI : OrderTopology (Fin 3) := ⟨rfl⟩
  letI : RegularSpace (Fin 3) := exercise_31_3_assumed (inferInstance : OrderTopology (Fin 3))
  have hopen : IsOpen ({0} : Set (Fin 3)) := by
    apply TopologicalSpace.isOpen_generateFrom_of_mem
    refine ⟨1, Or.inr ?_⟩
    ext a
    change (a = 0 ↔ ((a = 1 ∨ (a = 0 ∧ (1 : Fin 3) = 1)) ∧
      ¬((1 : Fin 3) = a ∨ (1 = 0 ∧ a = 1))))
    fin_cases a <;> simp
  have hr : ∀ (x : Fin 3), ∀ s ∈ 𝓝 x, ∃ t ∈ 𝓝 x, IsClosed t ∧ t ⊆ s :=
    ((regularSpace_TFAE (Fin 3)).out 0 3).mp (inferInstance : RegularSpace (Fin 3))
  obtain ⟨t, ht, htclosed, hts⟩ := hr 0 {0} (hopen.mem_nhds (by simp))
  have h0t : 0 ∈ t := mem_of_mem_nhds ht
  have hteq : t = {0} := by
    apply Set.Subset.antisymm hts
    simpa [Set.singleton_subset_iff]
  have hopen' : IsOpen ({0}ᶜ : Set (Fin 3)) := by
    simpa [hteq] using htclosed.isOpen_compl
  have hgeneric : ∀ u : Set (Fin 3), IsOpen u → 2 ∈ u → u = Set.univ := by
    intro u hu
    change TopologicalSpace.GenerateOpen g u at hu
    induction hu with
    | basic u hu =>
        rintro h2
        rcases hu with ⟨a, rfl | rfl⟩
        · change ((a = 2 ∨ (a = 0 ∧ (2 : Fin 3) = 1)) ∧ _) at h2
          omega
        · change (((2 : Fin 3) = a ∨ (2 = 0 ∧ a = 1)) ∧ _) at h2
          omega
    | univ => exact fun _ => rfl
    | inter u v _ _ ihu ihv =>
        intro h2
        rw [Set.mem_inter_iff] at h2
        rw [ihu h2.1, ihv h2.2, Set.univ_inter]
    | sUnion S _ ih =>
        intro h2
        obtain ⟨u, huS, h2u⟩ := Set.mem_sUnion.mp h2
        have := ih u huS h2u
        apply Set.eq_univ_of_univ_subset
        intro a _
        exact Set.mem_sUnion_of_mem (this ▸ Set.mem_univ a) huS
  have hcuniv : ({0}ᶜ : Set (Fin 3)) = Set.univ := hgeneric _ hopen' (by simp)
  have : (0 : Fin 3) ∈ ({0} : Set (Fin 3))ᶜ := hcuniv.symm ▸ Set.mem_univ 0
  simp at this
