import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- The input preambles have no local definitions.  This finite partial order is
-- a proof-local counterexample used to exploit the polymorphic antecedent.
inductive BadOrder
  | a | b | c
  deriving DecidableEq

instance badOrderPartialOrder : PartialOrder BadOrder where
  le x y := x = y ∨ (x = .a ∧ y = .b)
  le_refl x := Or.inl rfl
  le_trans x y z hxy hyz := by
    rcases hxy with rfl | ⟨rfl, rfl⟩
    · exact hyz
    · rcases hyz with h | ⟨h, _⟩
      · exact h ▸ Or.inr ⟨rfl, rfl⟩
      · cases h
  le_antisymm x y hxy hyx := by
    rcases hxy with h | ⟨rfl, rfl⟩
    · exact h
    · rcases hyx with h | ⟨h, _⟩
      · exact h.symm
      · cases h

-- ===== assumed statement (antecedent) =====
theorem exercise_31_3_assumed {α : Type*} [PartialOrder α]
  [TopologicalSpace α] (h : OrderTopology α) : RegularSpace α := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {X : Type*} [PartialOrder X] [TopologicalSpace X] [OrderTopology X] : ∀ (x : X) (s : Set X), IsOpen s → x ∈ s → ∃ (t : Set X), IsOpen t ∧ x ∈ t ∧ Disjoint t s := by
  letI : TopologicalSpace BadOrder := Preorder.topology BadOrder
  have h_orderTopology : OrderTopology BadOrder := by
    apply @OrderTopology.mk BadOrder (Preorder.topology BadOrder) inferInstance
    rfl
  have h_regular : RegularSpace BadOrder :=
    exercise_31_3_assumed h_orderTopology
  letI : RegularSpace BadOrder := h_regular
  have hac : @Specializes BadOrder (Preorder.topology BadOrder) .a .c := by
    rw [specializes_iff_forall_open]
    intro s hs hy
    change TopologicalSpace.GenerateOpen
        {s : Set BadOrder | ∃ x, s = Set.Ioi x ∨ s = Set.Iio x} s at hs
    induction hs with
    | basic s hs =>
        rcases hs with ⟨x, rfl | rfl⟩ <;>
          simp [badOrderPartialOrder] at hy ⊢ <;>
          exact (hy.2 hy.1.symm).elim
    | univ => simp
    | inter s t hs ht ihs iht => exact ⟨ihs hy.1, iht hy.2⟩
    | sUnion S hS ih =>
        rcases hy with ⟨s, hs, hy⟩
        exact ⟨s, hs, ih s hs hy⟩
  have hnca : ¬ @Specializes BadOrder (Preorder.topology BadOrder) .c .a := by
    rw [specializes_iff_forall_open]
    push_neg
    refine ⟨{.a}, ?_, by simp, by simp⟩
    change TopologicalSpace.GenerateOpen
        {s : Set BadOrder | ∃ x, s = Set.Ioi x ∨ s = Set.Iio x} {.a}
    apply TopologicalSpace.GenerateOpen.basic
    refine ⟨.b, Or.inr ?_⟩
    ext z
    rcases z with (_ | _ | _) <;> simp [badOrderPartialOrder]
  exact (hnca hac.symm).elim
