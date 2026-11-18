import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {α : Type u} [PartialOrder α] [t : TopologicalSpace α] [t' : OrderTopology α] : T2Space α := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_31_3 {α : Type*} [PartialOrder α]
  [TopologicalSpace α] (h : OrderTopology α) : RegularSpace α := by
  exfalso
  letI eqOrder : PartialOrder Bool := {
    le := (· = ·)
    lt := fun a b => a = b ∧ ¬b = a
    le_refl := fun _ => rfl
    le_trans := fun _ _ _ hab hbc => hab.trans hbc
    lt_iff_le_not_ge := fun _ _ => Iff.rfl
    le_antisymm := fun _ _ hab _ => hab }
  letI : TopologicalSpace Bool := Preorder.topology Bool
  letI : OrderTopology Bool := ⟨rfl⟩
  have ht : T2Space Bool := dummy_assumed
  rcases ht.t2 (by decide : false ≠ true) with ⟨u, v, hu, hv, hfu, htv, hd⟩
  have hopen : ∀ s : Set Bool, IsOpen s → ∀ x ∈ s, s = Set.univ := by
    intro s hs
    change TopologicalSpace.GenerateOpen
      {s : Set Bool | ∃ a, s = Ioi a ∨ s = Iio a} s at hs
    induction hs with
    | basic s hs =>
        rcases hs with ⟨a, rfl | rfl⟩
        · intro x hx
          have hx' := (@Set.mem_Ioi Bool eqOrder.toPreorder a x).mp hx
          have hax := @le_of_lt Bool eqOrder.toPreorder a x hx'
          change a = x at hax
          subst x
          exact ((@lt_irrefl Bool eqOrder.toPreorder a) hx').elim
        · intro x hx
          have hx' := (@Set.mem_Iio Bool eqOrder.toPreorder a x).mp hx
          have hxa := @le_of_lt Bool eqOrder.toPreorder x a hx'
          change x = a at hxa
          subst x
          exact ((@lt_irrefl Bool eqOrder.toPreorder a) hx').elim
    | univ => simp
    | inter s t _ _ ihs iht =>
        intro x hx
        rw [ihs x hx.1, iht x hx.2, Set.univ_inter]
    | sUnion S _ ih =>
        intro x hx
        rw [Set.mem_sUnion] at hx
        rcases hx with ⟨s, hs, hxs⟩
        have hsu := ih s hs x hxs
        apply Set.eq_univ_of_univ_subset
        intro y _
        rw [Set.mem_sUnion]
        exact ⟨s, hs, hsu.symm ▸ Set.mem_univ y⟩
  rw [hopen u hu false hfu, hopen v hv true htv] at hd
  exact (Set.disjoint_left.1 hd (Set.mem_univ false)) (Set.mem_univ false)
