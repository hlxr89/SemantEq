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
theorem dummy {X : Type*} [Preorder X] [TopologicalSpace X] : RegularSpace X := by
  letI : PartialOrder (Fin 3) := {
    le x y := x = y ∨ (x = 0 ∧ y = 1)
    lt x y := x = 0 ∧ y = 1
    le_refl x := Or.inl rfl
    le_trans a b c hab hbc := by
      rcases hab with rfl | ⟨rfl, rfl⟩
      · exact hbc
      · rcases hbc with h | ⟨h, _⟩
        · exact h ▸ Or.inr ⟨rfl, rfl⟩
        · norm_num at h
    le_antisymm a b hab hba := by
      rcases hab with h | ⟨ha, hb⟩
      · exact h
      · rcases hba with h | ⟨h, _⟩
        · exact h.symm
        · omega
    lt_iff_le_not_ge a b := by
      constructor
      · rintro ⟨rfl, rfl⟩
        norm_num
      · rintro ⟨h | ⟨h, h'⟩, hn⟩
        · exact False.elim (hn (Or.inl h.symm))
        · exact ⟨h, h'⟩ }
  letI : TopologicalSpace (Fin 3) :=
    TopologicalSpace.generateFrom {s | ∃ a, s = Set.Ioi a ∨ s = Set.Iio a}
  have hot : OrderTopology (Fin 3) := ⟨rfl⟩
  letI : RegularSpace (Fin 3) := exercise_31_3_assumed hot
  have hspec : (0 : Fin 3) ⤳ (2 : Fin 3) := by
    rw [specializes_iff_forall_open]
    intro s hs h2
    change TopologicalSpace.GenerateOpen _ s at hs
    induction hs with
    | basic s hs =>
        rcases hs with ⟨a, rfl | rfl⟩
        · simp only [mem_Ioi] at h2
          rcases h2 with ⟨_, h⟩
          have := congrArg Fin.val h
          norm_num at this
        · simp only [mem_Iio] at h2
          rcases h2 with ⟨h, _⟩
          have := congrArg Fin.val h
          norm_num at this
    | univ => simp
    | inter s t _ _ ihs iht => exact ⟨ihs h2.1, iht h2.2⟩
    | sUnion S _ ih =>
        rcases h2 with ⟨s, hsS, h2s⟩
        exact ⟨s, hsS, ih s hsS h2s⟩
  have hrev : (2 : Fin 3) ⤳ (0 : Fin 3) := hspec.symm
  have hopen : IsOpen ({0} : Set (Fin 3)) := by
    apply isOpen_generateFrom_of_mem
    refine ⟨1, Or.inr ?_⟩
    ext x
    change (x = 0) ↔ (x = 0 ∧ (1 : Fin 3) = 1)
    simp
  have hbad := hrev.mem_open hopen (by simp)
  simp at hbad
